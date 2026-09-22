/**
 * Keeps the lowest adaptive bitrate level of an hls.js stream loaded past the end of the buffer, and every level's
 * playlist loaded in advance. When the connection breaks down, playback drops to the lowest level at once instead of
 * waiting for its playlist, a new transcode and a download. The server runs that level as a transcode of its own,
 * next to the level playing.
 *
 * The ladder also reaches above the bitrate the client measured at playback start, for a connection that gets better
 * later. Levels above the ones playback has already used are only opened up once the connection has held up for a
 * while, so a link that comes and goes does not restart the server's encoder over and over.
 */

// Seconds of the lowest level kept loaded past the end of the buffer
const FLOOR_AHEAD = 30;
// Below this many buffered seconds, a fragment that will not arrive in time is given up for the lowest level
const RESCUE_BUFFER = 4;
// Buffered seconds the lowest level has to build up before playback may climb again after a drop
const RECOVER_BUFFER = 10;
const CHECK_INTERVAL = 250;
// Seconds of buffer a level picked by hand leaves in place, so its transcode has time to start
const SWITCH_MARGIN = 10;
// Seconds the connection has to carry a level playback has not used yet before it is opened up
const CLIMB_STEADY = 30;
// Seconds between two of those steps up, so a link that comes and goes does not restart the encoder each time
const CLIMB_DWELL = 60;
// Headroom over such a level's bitrate the connection has to show for all of CLIMB_STEADY
const CLIMB_HEADROOM = 1.4;
// Older browsers play on as before, without the lowest level kept loaded
const isSupported = typeof AbortController !== 'undefined' && typeof ReadableStream !== 'undefined';

function parsePlaylist(text, baseUrl) {
    const segments = [];
    let initUrl = null;
    let sn = 0;
    let start = 0;
    let duration = 0;

    for (const rawLine of text.split('\n')) {
        const line = rawLine.trim();
        if (line.startsWith('#EXT-X-MEDIA-SEQUENCE:')) {
            sn = parseInt(line.slice('#EXT-X-MEDIA-SEQUENCE:'.length), 10);
        } else if (line.startsWith('#EXT-X-MAP:')) {
            const uri = /URI="([^"]+)"/.exec(line);
            initUrl = uri ? new URL(uri[1], baseUrl).href : null;
        } else if (line.startsWith('#EXTINF:')) {
            duration = parseFloat(line.slice('#EXTINF:'.length));
        } else if (line && !line.startsWith('#')) {
            segments.push({ sn: sn++, start, end: start + duration, url: new URL(line, baseUrl).href });
            start += duration;
        }
    }

    return { initUrl, segments };
}

/**
 * Creates the loaders to pass to the hls.js config, then attach() the hls.js instance.
 */
export function createHlsFloorLevel(media, includeCorsCredentials, maxStreamingBitrate) {
    const DefaultLoader = Hls.DefaultConfig.loader;
    const credentials = includeCorsCredentials ? 'include' : 'same-origin';
    // Downloaded fragments of the lowest level by sequence number, and its init segment as 'init'
    const cache = new Map();
    // Level playlists by level index: { text, url, promise }
    const playlists = new Map();
    // Timing of the last few fragments downloaded, by URL: { ttfb, transfer }
    const downloads = new Map();
    // Media fragments fetched ahead of their level's init segment, by "level:sn": { promise, controller, time }
    const beforeInit = new Map();
    let hls = null;
    let level = -1;
    // Segments of the lowest level
    let floor = null;
    // When to fetch the next playlist, -1 while none is due
    let playlistsDue = -1;
    let inflight = null;
    // Bytes per millisecond of the last completed download
    let lastRate = 0;
    // Fragments hls.js is loading itself: one of a higher level, and one of the lowest level missing from the cache
    let mainLoad = null;
    let floorLoad = null;
    // A higher level's init segment hls.js waits for, with its media fragment fetched first
    let initLoad = null;
    // Set by a drop to the lowest level or a failed fragment, until downloads show the connection is back
    let recovering = false;
    // Set by a drop to the lowest level, until it has buffered RECOVER_BUFFER again, so playback does not bounce
    let holding = false;
    let recentRates = [];
    // Highest bitrate playback may use on Auto: what the client's measured bitrate bought at playback start, plus
    // what the connection has proven it carries since. Levels above it stay closed. 0 while there is no ladder.
    let ceilingBitrate = 0;
    // When the ceiling last moved, and since when the connection has carried the level above it
    let ceilingAt = 0;
    let steadySince = 0;
    let timer = null;

    function isFloorFragment(frag) {
        return level !== -1 && frag?.type === 'main' && frag.level === level;
    }

    // Level indexes from the lowest bitrate up. The master playlist lists the level the client asked for first,
    // so an index says nothing about bitrate.
    function byBitrate() {
        return hls.levels.map((_, index) => index).sort((a, b) => hls.levels[a].bitrate - hls.levels[b].bitrate);
    }

    // The highest level within the ceiling
    function ceilingLevel() {
        const ascending = byBitrate();
        return ascending.filter(index => hls.levels[index].bitrate <= ceilingBitrate).pop() ?? ascending[0];
    }

    function isLoading(load) {
        return load && load.frag.loader === load.loader && !load.loader.stats.aborted && !load.loader.stats.loading.end;
    }

    function download(key, url) {
        /* eslint-disable-next-line compat/compat */
        const controller = new AbortController();
        const entry = { key, controller, start: performance.now(), first: 0, loaded: 0 };
        entry.promise = (async () => {
            try {
                const response = await fetch(url, { credentials, signal: controller.signal });
                if (!response.ok) {
                    return null;
                }
                entry.first = performance.now();
                const reader = response.body.getReader();
                const chunks = [];
                for (;;) {
                    const { done, value } = await reader.read();
                    if (done) break;
                    chunks.push(value);
                    entry.loaded += value.length;
                }
                const end = performance.now();
                const data = new Uint8Array(entry.loaded);
                let offset = 0;
                for (const chunk of chunks) {
                    data.set(chunk, offset);
                    offset += chunk.length;
                }
                lastRate = entry.loaded / Math.max(end - entry.first, 1);
                if (!hls) {
                    return null;
                }
                if (recovering) {
                    recover(lastRate * 8000);
                }
                const result = { data: data.buffer, ttfb: entry.first - entry.start };
                cache.set(key, result);
                return result;
            } catch {
                return null;
            } finally {
                if (inflight === entry) {
                    inflight = null;
                }
            }
        })();
        inflight = entry;
    }

    // Link speed as the downloads of the lowest level see it, including one stuck right now
    function currentRate() {
        const now = performance.now();
        if (inflight?.first && now - inflight.first > 500) {
            return Math.min(lastRate || Infinity, inflight.loaded / (now - inflight.first));
        }
        if (inflight && !inflight.first && now - inflight.start > 5000) {
            return 0;
        }
        return lastRate;
    }

    // Once two downloads of the lowest level show the connection is back, lets playback climb at once:
    // hls.js never returns to a level whose fragments failed, and an outage fails them all
    function recover(bitsPerSecond) {
        const floorBitrate = hls.levels[level].bitrate;
        const nextBitrate = Math.min(...hls.levels.map(candidate => candidate.bitrate).filter(bitrate => bitrate > floorBitrate));
        recentRates = [...recentRates.slice(-1), bitsPerSecond];
        if (recentRates.length < 2 || Math.min(...recentRates) <= 2 * nextBitrate) return;
        if (getBufferEnd() - media.currentTime < RECOVER_BUFFER) return;

        const rate = Math.min(...recentRates);
        console.debug(`[hlsFloorLevel] connection is back at ${Math.round(rate / 1000)} kbps`);
        recovering = false;
        recentRates = [];
        for (const candidate of hls.levels) {
            candidate.fragmentError = 0;
            candidate.loadError = 0;
        }
        // The estimate still holds the outage
        if (hls.loadLevel === level) {
            hls.bandwidthEstimate = rate;
        }
    }

    // Hands a downloaded fragment to hls.js, timed like a download at the current link speed, so its bandwidth
    // estimate keeps following the connection while playback runs on the lowest level. A stuck link counts as
    // one fragment duration, so an outage does not outweigh everything after it.
    function serve(loader, entry, context, callbacks) {
        const stats = loader.stats;
        const now = performance.now();
        const rate = currentRate();
        const longest = (context.frag.duration || 3) * 1000;
        const transfer = rate > 0 ? Math.min(entry.data.byteLength / rate, longest) : longest;
        stats.loading.start = now - transfer - entry.ttfb;
        stats.loading.first = now - transfer;
        stats.loading.end = now;
        stats.loaded = stats.total = entry.data.byteLength;
        stats.chunkCount = 1;
        // hls.js hands the buffer on to its worker, so it gets a copy
        callbacks.onSuccess({ url: context.url, data: entry.data.slice(0) }, stats, context, null);
    }

    // Hands over a fragment fetched ahead, timed like the download it was
    function serveTimed(loader, result, context, callbacks) {
        downloads.set(context.url, { ttfb: result.ttfb, transfer: result.transfer });
        const stats = loader.stats;
        stats.loading.end = performance.now();
        stats.loading.first = stats.loading.end - result.transfer;
        stats.loading.start = stats.loading.first - result.ttfb;
        stats.loaded = stats.total = result.data.byteLength;
        stats.chunkCount = 1;
        callbacks.onSuccess({ url: context.url, data: result.data }, stats, context, null);
    }

    function fetchAhead(key, url) {
        /* eslint-disable-next-line compat/compat */
        const controller = new AbortController();
        const entry = { controller, time: performance.now() };
        entry.promise = (async () => {
            try {
                const response = await fetch(url, { credentials, signal: controller.signal });
                if (!response.ok) return null;
                const first = performance.now();
                const data = await response.arrayBuffer();
                return { data, ttfb: first - entry.time, transfer: performance.now() - first };
            } catch {
                return null;
            }
        })();
        beforeInit.set(key, entry);
        return entry;
    }

    // Where hls.js loads next: the end of the buffer, or its start position before playback has begun
    function getLoadPosition() {
        if (media.buffered.length || media.currentTime > 0) return getBufferEnd();
        return Math.max(hls.config.startPosition, 0);
    }

    // hls.js loads a fragment again when a seek lands during its first load, as at playback start with a resume
    // position. The browser cache answers the repeat at once, and hls.js would take that for a very fast link.
    // The repeat gets the timing of the real download instead.
    function timed(onSuccess) {
        return (response, stats, context, networkDetails) => {
            const earlier = downloads.get(context.url);
            if (earlier) {
                stats.loading.first = stats.loading.end - earlier.transfer;
                stats.loading.start = stats.loading.first - earlier.ttfb;
            } else {
                downloads.set(context.url, { ttfb: stats.loading.first - stats.loading.start, transfer: stats.loading.end - stats.loading.first });
                if (downloads.size > 8) downloads.delete(downloads.keys().next().value);
            }
            onSuccess(response, stats, context, networkDetails);
        };
    }

    class FragmentLoader extends DefaultLoader {
        #pending = null;

        #wait(context, callbacks, promise, then) {
            this.context = context;
            this.callbacks = callbacks;
            const request = this.#pending = { cancelled: false };
            promise.then(result => {
                if (request.cancelled) return;
                this.#pending = null;
                then(result);
            });
        }

        load(context, config, callbacks) {
            const frag = context.frag;
            const loadItself = () => super.load(context, config, frag?.type === 'main' ? { ...callbacks, onSuccess: timed(callbacks.onSuccess) } : callbacks);
            if (isFloorFragment(frag)) {
                const key = frag.sn === 'initSegment' ? 'init' : frag.sn;
                const entry = cache.get(key);
                const pending = entry ? Promise.resolve(entry) : (inflight?.key === key && inflight.promise);
                if (pending) {
                    this.#wait(context, callbacks, pending, result => (result ? serve(this, result, context, callbacks) : loadItself()));
                    return;
                }
                floorLoad = { loader: this, frag };
            } else if (frag?.type === 'main' && frag.sn === 'initSegment') {
                // A level's init segment alone starts its transcode at the very beginning of the film. The media
                // fragment playback needs goes first, so its request starts the transcode there, and the init follows.
                const next = hls.levels[frag.level]?.details?.fragments.find(candidate => candidate.start + candidate.duration > getLoadPosition() + 0.05);
                if (next) {
                    initLoad = { loader: this, frag };
                    const key = `${frag.level}:${next.sn}`;
                    this.#wait(context, callbacks, (beforeInit.get(key) ?? fetchAhead(key, next.url)).promise, loadItself);
                    return;
                }
            } else if (frag?.type === 'main' && typeof frag.sn === 'number') {
                mainLoad = { loader: this, frag };
                const key = `${frag.level}:${frag.sn}`;
                const entry = beforeInit.get(key);
                if (entry) {
                    beforeInit.delete(key);
                    this.#wait(context, callbacks, entry.promise, result => (result ? serveTimed(this, result, context, callbacks) : loadItself()));
                    return;
                }
            }
            loadItself();
        }

        abort() {
            if (this.#pending) {
                this.#pending.cancelled = true;
                this.#pending = null;
                this.stats.aborted = true;
                this.callbacks?.onAbort?.(this.stats, this.context, null);
                return;
            }
            super.abort();
        }

        destroy() {
            if (this.#pending) {
                this.#pending.cancelled = true;
                this.#pending = null;
            }
            super.destroy();
        }
    }

    // Serves level playlists fetched in advance: a switch then never waits for one, nor aborts one half loaded
    class PlaylistLoader extends DefaultLoader {
        #pending = null;

        load(context, config, callbacks) {
            const entry = context.type === 'level' ? playlists.get(context.level) : null;
            if (!entry) {
                super.load(context, config, callbacks);
                return;
            }
            this.context = context;
            this.callbacks = callbacks;
            const request = this.#pending = { cancelled: false };
            // A fetch still running when this loader would have timed out counts as a timeout
            request.timeout = setTimeout(() => {
                request.cancelled = true;
                this.#pending = null;
                callbacks.onTimeout(this.stats, context, null);
            }, config.timeout || 20000);
            entry.promise.then(result => {
                if (request.cancelled) return;
                clearTimeout(request.timeout);
                this.#pending = null;
                if (!result) {
                    super.load(context, config, callbacks);
                    return;
                }
                const stats = this.stats;
                stats.loading.start = stats.loading.first = stats.loading.end = performance.now();
                stats.loaded = stats.total = result.text.length;
                callbacks.onSuccess({ url: context.url, data: result.text }, stats, context, null);
            });
        }

        abort() {
            if (this.#pending) {
                this.#pending.cancelled = true;
                clearTimeout(this.#pending.timeout);
                this.#pending = null;
                this.stats.aborted = true;
                this.callbacks?.onAbort?.(this.stats, this.context, null);
                return;
            }
            super.abort();
        }

        destroy() {
            if (this.#pending) {
                this.#pending.cancelled = true;
                clearTimeout(this.#pending.timeout);
                this.#pending = null;
            }
            super.destroy();
        }
    }

    function fetchPlaylist(index) {
        const entry = { text: null, url: hls.levels[index].uri };
        entry.promise = (async () => {
            try {
                const response = await fetch(entry.url, { credentials });
                if (!response.ok) throw new Error(`HTTP ${response.status}`);
                entry.text = await response.text();
                entry.url = response.url || entry.url;
            } catch (err) {
                console.debug(`[hlsFloorLevel] playlist of level ${index} failed to load`, err);
                playlists.delete(index);
                playlistsDue = performance.now() + 10000;
            }
            return entry.text ? entry : null;
        })();
        playlists.set(index, entry);
        return entry.promise;
    }

    // One playlist at a time, from the lowest level up, for every level hls.js has not loaded itself
    function loadPlaylists() {
        const floorDetails = hls.levels[level].details;
        if (!floor && floorDetails) {
            floor = {
                initUrl: floorDetails.fragments[0]?.initSegment?.url ?? null,
                segments: floorDetails.fragments.map(frag => ({ sn: frag.sn, start: frag.start, end: frag.start + frag.duration, url: frag.url }))
            };
        }
        if (playlistsDue === -1 || performance.now() < playlistsDue) return;
        if ([...playlists.values()].some(entry => !entry.text)) return;

        const next = byBitrate().find(index => !playlists.has(index) && !hls.levels[index].details);
        if (next === undefined) {
            playlistsDue = -1;
            return;
        }
        fetchPlaylist(next).then(entry => {
            if (entry && hls && next === level && !floor) {
                floor = parsePlaylist(entry.text, entry.url);
            }
        });
    }

    // End of the buffered range that playback runs into, allowing for small holes
    function getBufferEnd() {
        const time = media.currentTime;
        const ranges = media.buffered;
        let end = time;
        for (let i = 0; i < ranges.length; i++) {
            if (ranges.start(i) <= end + 0.5 && ranges.end(i) > end) {
                end = ranges.end(i);
            }
        }
        return end;
    }

    function prefetch(bufferEnd) {
        const { segments } = floor;
        const first = segments[0]?.sn ?? 0;
        for (const key of cache.keys()) {
            const segment = segments[key - first];
            if (key !== 'init' && (!segment || segment.end < media.currentTime || segment.start > bufferEnd + FLOOR_AHEAD * 2)) {
                cache.delete(key);
            }
        }

        const hlsLoading = isLoading(floorLoad) ? floorLoad.frag.sn : null;
        let wanted = null;
        let index = segments.findIndex(segment => segment.end > bufferEnd);
        for (; index !== -1 && index < segments.length && segments[index].start < bufferEnd + FLOOR_AHEAD; index++) {
            if (!cache.has(segments[index].sn) && segments[index].sn !== hlsLoading) {
                wanted = segments[index];
                break;
            }
        }

        if (inflight) {
            // A seek moved the window away from the download
            const segment = inflight.key === 'init' ? null : segments[inflight.key - first];
            if (segment && (segment.end < media.currentTime || segment.start > bufferEnd + FLOOR_AHEAD)) {
                inflight.controller.abort();
            }
            return;
        }

        // The init segment only after a media segment: a request for it starts the transcode at the beginning
        if (cache.size && !cache.has('init') && floor.initUrl) {
            download('init', floor.initUrl);
        } else if (wanted) {
            download(wanted.sn, wanted.url);
        }
    }

    // Drops to the lowest level, already downloaded, when the buffer is about to run dry and nothing arrives in
    // time: a fragment loading too slowly, or none loading at all while hls.js waits for something else
    function rescue(bufferEnd) {
        // Not before playback has its first fragment: hls.js does not recover from an abort of that one
        if (!hls.autoLevelEnabled || media.paused || media.seeking || !media.buffered.length || hls.loadLevel === level) return;
        const ahead = bufferEnd - media.currentTime;
        if (ahead >= RESCUE_BUFFER) return;

        let load = null;
        if (isLoading(mainLoad)) {
            load = mainLoad;
        } else if (isLoading(initLoad)) {
            load = initLoad;
        }
        const sn = typeof load?.frag.sn === 'number' ? load.frag.sn : floor.segments.find(segment => segment.end > bufferEnd + 0.05)?.sn;
        if (!cache.has(sn) || !cache.has('init')) return;

        const now = performance.now();
        let arrival = 0;
        if (load?.loader.stats.loading.first && load.loader.stats.loaded) {
            const { frag, loader: { stats } } = load;
            const total = stats.total || (frag.duration * hls.levels[frag.level].bitrate) / 8;
            arrival = (total - stats.loaded) / (stats.loaded / Math.max(now - stats.loading.first, 1)) / 1000;
        } else if ((load && now - load.loader.stats.loading.start > 1500) || ahead < 1.5) {
            arrival = Infinity;
        }
        if (arrival < ahead - 1) return;

        let reason = 'nothing is loading';
        if (load) {
            reason = (load === initLoad ? 'the init segment' : 'fragment ' + sn) + ' of level ' + load.frag.level + ' is late';
        }
        console.debug(`[hlsFloorLevel] ${reason} with ${ahead.toFixed(1)}s buffered, dropping to level ${level}`);
        mainLoad = null;
        initLoad = null;
        recovering = true;
        holding = true;
        recentRates = [];
        hls.bandwidthEstimate = hls.levels[level].bitrate;
        hls.nextLoadLevel = level;
        load?.frag.abortRequests();
    }

    // Opens the ceiling up to what the connection carries, once it has carried it for CLIMB_STEADY: a stream
    // started on a bad link climbs to the quality it would have got on a good one, without a restart. Levels
    // playback has already used are below the ceiling and stay open, so a recovery after an outage is not held up.
    function climb(bufferEnd) {
        const ascending = byBitrate();
        const next = ascending.find(index => hls.levels[index].bitrate > ceilingBitrate);
        const now = performance.now();
        if (next === undefined
            || recovering
            || holding
            || media.paused
            || hls.bandwidthEstimate < hls.levels[next].bitrate * CLIMB_HEADROOM
            || bufferEnd - media.currentTime < RECOVER_BUFFER) {
            steadySince = 0;
            return;
        }

        if (!steadySince) {
            steadySince = now;
            return;
        }
        if (now - steadySince < CLIMB_STEADY * 1000 || now - ceilingAt < CLIMB_DWELL * 1000) return;

        // Everything the connection carries, not one level per step: it has held up for CLIMB_STEADY by now
        const reached = ascending.filter(index => hls.levels[index].bitrate * CLIMB_HEADROOM <= hls.bandwidthEstimate).pop();
        ceilingBitrate = hls.levels[reached].bitrate;
        ceilingAt = now;
        steadySince = 0;
        console.debug(`[hlsFloorLevel] connection carries ${Math.round(hls.bandwidthEstimate / 1000)} kbps, levels up to ${Math.round(ceilingBitrate / 1000)} kbps opened up`);
    }

    function tick() {
        if (level === -1) return;
        loadPlaylists();
        // A quality picked by hand stays, whatever the connection does
        if (!floor || !hls.autoLevelEnabled) return;
        const bufferEnd = getBufferEnd();
        if (holding && bufferEnd - media.currentTime >= RECOVER_BUFFER) {
            holding = false;
        }
        for (const [key, entry] of beforeInit) {
            if (performance.now() - entry.time > 30000) {
                entry.controller.abort();
                beforeInit.delete(key);
            }
        }
        climb(bufferEnd);
        rescue(bufferEnd);
        prefetch(getLoadPosition());
    }

    function findFloorLevel() {
        const levels = hls.levels;
        level = levels.length < 2 ? -1 : levels.reduce((lowest, candidate, index) => (candidate.bitrate < levels[lowest].bitrate ? index : lowest), 0);

        // The ladder reaches above the bitrate the client measured at playback start. Playback begins at that
        // bitrate, as it always did, and the connection has to prove itself for the levels above it.
        // The level built for that bitrate carries audio on top of it, so it can sit a little above; the level above
        // it is at least double, so half again is a safe line between them.
        if (level !== -1 && !ceilingBitrate) {
            const start = byBitrate().filter(index => !maxStreamingBitrate || hls.levels[index].bitrate <= maxStreamingBitrate * 1.5).pop();
            ceilingBitrate = hls.levels[start ?? level].bitrate;
            ceilingAt = performance.now();
        }
    }

    // Switches to a level picked by hand, or back to Auto (-1), without a rebuffer: what plays in the next
    // SWITCH_MARGIN seconds stays, and the buffer after it is replaced by the new level. hls.js would keep only
    // about one fragment, too little for a transcode that has to start first.
    function switchLevel(index) {
        hls.loadLevel = index;
        // A level picked by hand above the ceiling was asked for: Auto keeps it afterwards
        if (index !== -1 && hls.levels[index].bitrate > ceilingBitrate) {
            ceilingBitrate = hls.levels[index].bitrate;
            ceilingAt = performance.now();
            steadySince = 0;
        }

        const keep = media.currentTime + (index === level ? 1 : SWITCH_MARGIN);
        if (getBufferEnd() <= keep) return;
        for (const load of [mainLoad, floorLoad]) {
            if (isLoading(load)) load.frag.abortRequests();
        }
        hls.trigger(Hls.Events.BUFFER_FLUSHING, { startOffset: keep, endOffset: Number.POSITIVE_INFINITY, type: null });
    }

    function destroy() {
        clearInterval(timer);
        inflight?.controller.abort();
        cache.clear();
        playlists.clear();
        downloads.clear();
        for (const entry of beforeInit.values()) entry.controller.abort();
        beforeInit.clear();
        hls = null;
        level = -1;
        floor = null;
        mainLoad = null;
        floorLoad = null;
        initLoad = null;
        ceilingBitrate = 0;
        steadySince = 0;
    }

    function attach(instance) {
        hls = instance;
        if (!isSupported) return;
        hls.on(Hls.Events.MANIFEST_PARSED, findFloorLevel);
        hls.on(Hls.Events.LEVELS_UPDATED, findFloorLevel);
        // From the first fragment on, so the lowest level is there if the start turns out too slow
        hls.on(Hls.Events.FRAG_LOADING, (_event, data) => {
            if (level !== -1 && playlists.size === 0 && playlistsDue === -1 && data.frag.type === 'main') {
                playlistsDue = 0;
            }
        });
        hls.on(Hls.Events.ERROR, (_event, data) => {
            if (data.frag?.type === 'main' && (data.details === Hls.ErrorDetails.FRAG_LOAD_TIMEOUT || data.details === Hls.ErrorDetails.FRAG_LOAD_ERROR)) {
                recovering = true;
                recentRates = [];
            }
        });
        // hls.js forgets a forced level after one fragment, so the hold, and the ceiling over the levels the
        // connection has not carried yet, ask for their level again after each one
        hls.on(Hls.Events.FRAG_LOADED, (_event, data) => {
            if (!hls.autoLevelEnabled || data.frag.type !== 'main') return;
            if (holding) {
                hls.nextLoadLevel = level;
            } else if (ceilingBitrate && hls.levels[hls.nextAutoLevel]?.bitrate > ceilingBitrate) {
                hls.nextLoadLevel = ceilingLevel();
            }
        });
        hls.on(Hls.Events.DESTROYING, destroy);
        timer = setInterval(tick, CHECK_INTERVAL);
    }

    return { FragmentLoader, PlaylistLoader, attach, switchLevel };
}
