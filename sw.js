const CACHE_NAME = 'minecraft-web-v2';
const ASSETS_TO_CACHE = [
    './',
    './index.html',
    './index.js',
    './index.wasm',
    './mc_platform.js',
    './saves.js',
    './manifest.json'
];

const SOUND_CACHE = 'mcre-sounds-v1';

function isSoundFile(url) {
    return url.pathname.indexOf('/sounds/') !== -1 && url.pathname.slice(-4) === '.ogg';
}

function soundResponse(request) {
    const key = request.url;
    return caches.open(SOUND_CACHE).then(cache =>
        cache.match(key).then(hit => hit || fetch(key).then(response => {
            if (response && response.status === 200 && response.type === 'basic') {
                cache.put(key, response.clone());
            }
            return response;
        }))
    ).then(full => {
        const range = request.headers.get('range');
        if (!range || !full || full.status !== 200) return full;
        return full.arrayBuffer().then(buf => {
            const size = buf.byteLength;
            const type = full.headers.get('Content-Type') || 'audio/ogg';
            const m = /^bytes=(\d*)-(\d*)$/.exec(range.trim());
            if (!m || (m[1] === '' && m[2] === '')) {
                return new Response(buf, { status: 200, headers: { 'Content-Type': type } });
            }
            let start, end;
            if (m[1] === '') {
                start = Math.max(0, size - Number(m[2]));
                end = size - 1;
            } else {
                start = Number(m[1]);
                end = m[2] === '' ? size - 1 : Math.min(Number(m[2]), size - 1);
            }
            if (start >= size || start > end) {
                return new Response(null, { status: 416, headers: { 'Content-Range': 'bytes */' + size } });
            }
            return new Response(buf.slice(start, end + 1), {
                status: 206,
                headers: {
                    'Content-Type': type,
                    'Content-Range': 'bytes ' + start + '-' + end + '/' + size,
                    'Content-Length': String(end - start + 1),
                    'Accept-Ranges': 'bytes'
                }
            });
        });
    });
}

function needsIsolation(request) {
    return request.mode === 'navigate' || request.destination === 'worker' || request.destination === 'sharedworker';
}

function withIsolation(response) {
    if (!response || response.status === 0 || response.type === 'opaque' || response.type === 'opaqueredirect' ||
        response.type === 'cors' || response.type === 'error') {
        return response;
    }
    const headers = new Headers(response.headers);
    headers.set('Cross-Origin-Opener-Policy', 'same-origin');
    headers.set('Cross-Origin-Embedder-Policy', 'require-corp');
    return new Response(response.body, { status: response.status, statusText: response.statusText, headers: headers });
}

// Install event: cache core assets
self.addEventListener('install', event => {
    event.waitUntil(
        caches.open(CACHE_NAME)
            .then(cache => {
                console.log('Opened cache');
                return cache.addAll(ASSETS_TO_CACHE);
            })
            .then(() => self.skipWaiting())
    );
});

// Activate event: clean up old caches
self.addEventListener('activate', event => {
    event.waitUntil(
        caches.keys().then(cacheNames => {
            return Promise.all(
                cacheNames.map(cacheName => {
                    if (cacheName !== CACHE_NAME && cacheName !== SOUND_CACHE) {
                        return caches.delete(cacheName);
                    }
                })
            );
        }).then(() => self.clients.claim())
    );
});

// Fetch event: Network falling back to cache
self.addEventListener('fetch', event => {
    // Only intercept GET requests, and skip extensions like browser-sync if running locally
    if (event.request.method !== 'GET') return;
    if (new URL(event.request.url).pathname.indexOf('/api/') !== -1) return;
    if (isSoundFile(new URL(event.request.url))) {
        event.respondWith(soundResponse(event.request));
        return;
    }

    const isolate = needsIsolation(event.request);
    event.respondWith(
        fetch(event.request)
            .then(response => {
                // Check if we received a valid response
                if (!response || response.status !== 200 || response.type !== 'basic') {
                    return isolate ? withIsolation(response) : response;
                }

                // IMPORTANT: Clone the response. A response is a stream
                // and because we want the browser to consume the response
                // as well as the cache consuming the response, we need
                // to clone it so we have two streams.
                var responseToCache = response.clone();

                caches.open(CACHE_NAME)
                    .then(cache => {
                        cache.put(event.request, responseToCache);
                    });

                return isolate ? withIsolation(response) : response;
            })
            .catch(() => {
                // If network fails, fallback to cache
                return caches.match(event.request).then(response => {
                    if (response) {
                        return isolate ? withIsolation(response) : response;
                    }
                    // Could return a fallback offline page here if needed
                });
            })
    );
});
