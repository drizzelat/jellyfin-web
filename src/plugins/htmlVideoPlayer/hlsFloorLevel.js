/**
 * Keeps the lowest adaptive bitrate level of an hls.js stream loaded past the end of the buffer, and every level's
 * playlist loaded in advance. When the connection breaks down, playback drops to the lowest level at once instead of
 * waiting for its playlist, a new transcode and a download. The server runs that level as a transcode of its own,
 * next to the level playing.
 */

// Seconds of the lowest level kept loaded past the end of the buffer
const FLOOR_AHEAD = 30;
// Below this many buffered seconds, a fragment that will not arrive in time is given up for the lowest level
const RESCUE_BUFFER = 4;
// Buffered seconds the lowest level has to build up before playback may climb again after a drop
const RECOVER_BUFFER = 10;
const CHECK_INTERVAL = 250;
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
export function createHlsFloorLevel(media, includeCorsCredentials) {
    const DefaultLoader = Hls.DefaultConfig.loader;
    const credentials = includeCorsCredentials ? 'include' : 'same-origin';
    // Downloaded fragments of the lowest level by sequence number, and its init segment as 'init'
    const cache = new Map();
    // Level playlists by level index: { text, url, promise }
    const playlists = new Map();
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
    // Set by a drop to the lowest level or a failed fragment, until downloads show the connection is back
    let recovering = false;
    let recentRates = [];
    let timer = null;

    function isFloorFragment(frag) {
        return level !== -1 && frag?.type === 'main' && frag.level === level;
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

    class FragmentLoader extends DefaultLoader {
        #pending = null;

        load(context, config, callbacks) {
            const frag = context.frag;
            if (isFloorFragment(frag)) {
                const key = frag.sn === 'initSegment' ? 'init' : frag.sn;
                const entry = cache.get(key);
                const pending = entry ? Promise.resolve(entry) : (inflight?.key === key && inflight.promise);
                if (pending) {
                    this.context = context;
                    this.callbacks = callbacks;
                    const request = this.#pending = { cancelled: false };
                    pending.then(result => {
                        if (request.cancelled) return;
                        this.#pending = null;
                        if (result) {
                            serve(this, result, context, callbacks);
                        } else {
                            super.load(context, config, callbacks);
                        }
                    });
                    return;
                }
                floorLoad = { loader: this, frag };
            } else if (frag?.type === 'main' && typeof frag.sn === 'number') {
                mainLoad = { loader: this, frag };
            }
            super.load(context, config, callbacks);
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

        const byBitrate = hls.levels.map((_, index) => index).sort((a, b) => hls.levels[a].bitrate - hls.levels[b].bitrate);
        const next = byBitrate.find(index => !playlists.has(index) && !hls.levels[index].details);
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
        if (!hls.autoLevelEnabled || media.paused || media.seeking || hls.loadLevel === level) return;
        const ahead = bufferEnd - media.currentTime;
        if (ahead >= RESCUE_BUFFER) return;

        const load = isLoading(mainLoad) ? mainLoad : null;
        const sn = load ? load.frag.sn : floor.segments.find(segment => segment.end > bufferEnd + 0.05)?.sn;
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

        const reason = load ? 'fragment ' + sn + ' of level ' + load.frag.level + ' is late' : 'nothing is loading';
        console.debug(`[hlsFloorLevel] ${reason} with ${ahead.toFixed(1)}s buffered, dropping to level ${level}`);
        mainLoad = null;
        recovering = true;
        recentRates = [];
        hls.bandwidthEstimate = hls.levels[level].bitrate;
        hls.nextLoadLevel = level;
        load?.frag.abortRequests();
    }

    function tick() {
        if (level === -1) return;
        loadPlaylists();
        if (!floor) return;
        const bufferEnd = getBufferEnd();
        rescue(bufferEnd);
        prefetch(bufferEnd);
    }

    function findFloorLevel() {
        const levels = hls.levels;
        level = levels.length < 2 ? -1 : levels.reduce((lowest, candidate, index) => (candidate.bitrate < levels[lowest].bitrate ? index : lowest), 0);
    }

    function destroy() {
        clearInterval(timer);
        inflight?.controller.abort();
        cache.clear();
        playlists.clear();
        hls = null;
        level = -1;
        floor = null;
        mainLoad = null;
        floorLoad = null;
    }

    function attach(instance) {
        if (!isSupported) return;
        hls = instance;
        hls.on(Hls.Events.MANIFEST_PARSED, findFloorLevel);
        hls.on(Hls.Events.LEVELS_UPDATED, findFloorLevel);
        // Only once playback got its first fragment, so the playlists do not slow down the start
        hls.on(Hls.Events.FRAG_BUFFERED, (_event, data) => {
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
        hls.on(Hls.Events.DESTROYING, destroy);
        timer = setInterval(tick, CHECK_INTERVAL);
    }

    return { FragmentLoader, PlaylistLoader, attach };
}
