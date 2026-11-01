// ==UserScript==
// @name         Google Link Enhancer (kid4rm90s fork)
// @namespace    kid4rm90s
// @version      2026.11.01.004
// @description  Adds some extra WME functionality related to Google place links.
// @author       MapOMatic, WazeDev group, kid4rm90s
// @include      /^https:\/\/(www|beta)\.waze\.com\/(?!user\/)(.{2,6}\/)?editor\/?.*$/
// @license      GNU GPLv3
// ==/UserScript==
 /*
 * Google Link Enhancer (GLE) - Validates and enhances Google Place links in Waze Map Editor
 * Originally by MapOMatic, WazeDev group, forked and maintained by kid4rm90s
 * Usage:
 *   const linkEnhancer = new GoogleLinkEnhancer(wmeSDK, turf);
 *   await linkEnhancer.enable();   // or linkEnhancer.enable() without awaiting
 *
 * Works with both SDK modes. In 'async' mode (getWmeSdk({ mode: 'async' })) every SDK
 * module method returns a Promise, so all reads/writes here are awaited; with the default
 * synchronous SDK awaiting is a no-op. enable()/disable() return a Promise but may also
 * be called without awaiting — they handle their own errors.
 */

/* global google */

/* eslint-disable no-unused-vars */

/**
 * Google Link Enhancer - Validates and enhances Google Place links in Waze Map Editor
 * @class GoogleLinkEnhancer
 */
class GoogleLinkEnhancer {
    /**
     * Name of the map layer and of the Layer Switcher checkbox owned by this instance.
     * Public so a host script can recognise its own layer events.
     * @public
     */
    static LAYER_NAME = 'POI Shortcuts - GLE fork';

    // Configuration Constants
    static CONFIG = {
        CACHE: {
            NAME: 'gle_link_cache',
            CLEAN_INTERVAL_MIN: 1,
            LIFESPAN_HR: 6,
            MAX_SIZE: 1000
        },
        COLORS: {
            PERM_CLOSED: '#F00',
            TEMP_CLOSED: '#FD3',
            TOO_FAR: '#0FF',
            NOT_FOUND: '#F0F',
            DUPLICATE: '#FFA500',
            HIGHLIGHT: '#FF0',
            HIGHLIGHT_BG_ORANGE: '#FFA500',
            HIGHLIGHT_BG_RED: '#FAA',
            HIGHLIGHT_BG_YELLOW: '#FFA',
            HIGHLIGHT_BG_CYAN: '#0FF'
        },
        DEFAULTS: {
            DISTANCE_LIMIT: 400,
            POINT_TIMEOUT: 4000,
            API_DISABLE_DURATION: 10000,
            MAX_RETRY_CALLS: 30,
            RETRY_INTERVAL: 100
        },
        SELECTORS: {
            EXT_PROV_ELEM: 'wz-list-item.external-provider',
            EXT_PROV_ELEM_EDIT: 'wz-list-item.external-provider-edit',
            EXT_PROV_ELEM_CONTENT: 'div.external-provider-content'
        },
        STROKE: {
            POINT_WIDTH: '4',
            AREA_WIDTH: '12',
            LINE_WIDTH: 4,
            DASH_STYLE: '12 12',
            CLOSED_DASH_SHORT: '2 6',
            CLOSED_DASH_LONG: '2 16'
        }
    };

    #DISABLE_CLOSED_PLACES = false;
    #linkCache;
    #enabled = false;
    #disableApiUntil = null;
    #mapLayer = null;
    // Timestamp of the last programmatic Layer Switcher update, used to ignore the
    // toggle event the SDK may echo back for our own change.
    #layerCheckboxSyncAt = 0;
    #distanceLimit = GoogleLinkEnhancer.CONFIG.DEFAULTS.DISTANCE_LIMIT;
    #showTempClosedPOIs = true;
    #placesService;
    #linkObserver;
    #modeObserver;
    #searchResultsObserver;
    #lzString;
    #cacheCleanIntervalID;
    #originalHeadAppendChildMethod;
    #ptFeature;
    #lineFeature;
    #timeoutID;
    // external-provider-content element -> status tooltip we own. Kept so the value can
    // be restored if another script rewrites the title attribute (see
    // #startLinkTitleGuard()).
    #linkTitles = new WeakMap();
    #linkTitleObserver = null;
    // Incremented whenever a hover ends (or a new one starts) so an #addPoint call that is
    // still awaiting SDK reads can tell it has been superseded.
    #hoverSeq = 0;
    #processPlacesDebounced;
    #ready = null;
    strings = {
        permClosedPlace: 'Google indicates this place is permanently closed.\nVerify with other sources or your editor community before deleting.',
        tempClosedPlace: 'Google indicates this place is temporarily closed.',
        multiLinked: 'Linked more than once already. Please find and remove multiple links.',
        linkedToThisPlace: 'Already linked to this place',
        linkedNearby: 'Already linked to a nearby place',
        linkedToXPlaces: 'This is linked to {0} places',
        badLink: 'Invalid Google link. Please remove it.',
        tooFar: 'The Google linked place is more than {0} meters from the Waze place.  Please verify the link is correct.'
    };
 
    /* eslint-enable no-unused-vars */
    /**
     * Initialize Google Link Enhancer
     * @constructor
     * @param {Object} sdk - The WME SDK instance
     * @param {Object} trf - Turf.js library instance
     */
    constructor(sdk, trf) {
        this.sdk = sdk;
        this.trf = trf;
        const attributionElem = document.createElement('div');
        this.#placesService = new google.maps.places.PlacesService(attributionElem);
        this.#initLZString();
        this.#initCache();
        this.#processPlacesDebounced = this.#debounce(() => this.#processPlaces(), 300);

        // A constructor cannot await, so the async layer setup is stored and awaited by
        // everything that depends on it (#processPlaces, enable(), the initial check below).
        this.#ready = this.#initLayer();
        this.sdk.Events.trackDataModelEvents({ dataModelName: 'venues' });
        
        this.sdk.Events.on({
            eventName: 'wme-map-data-loaded',
            eventHandler: () => this.#processPlacesDebounced()
        });
        this.sdk.Events.on({
            eventName: 'wme-data-model-objects-changed',
            eventHandler: (evt) => {
                if (evt.dataModelName === 'venues') {
                    this.#processPlacesDebounced();
                }
            }
        });
        this.sdk.Events.on({
            eventName: 'wme-data-model-objects-added',
            eventHandler: (evt) => {
                if (evt.dataModelName === 'venues') {
                    this.#processPlacesDebounced();
                }
            }
        });
        this.sdk.Events.on({
            eventName: 'wme-data-model-objects-removed',
            eventHandler: (evt) => {
                if (evt.dataModelName === 'venues') {
                    this.#processPlacesDebounced();
                }
            }
        });
        // Redraw when the user ticks our Layer Switcher checkbox back on. #processPlaces()
        // clears the layer on every run but only draws while the checkbox is ticked, so
        // any data change made while the layer was hidden leaves it empty - the rings
        // (closed / not-found status included) would otherwise not come back until the
        // next venue change.
        this.sdk.Events.on({
            eventName: 'wme-layer-checkbox-toggled',
            eventHandler: (evt) => {
                if (!evt || evt.checked !== true) return;
                // Ignore the echo of our own #setLayerCheckboxChecked() call.
                if (Date.now() - this.#layerCheckboxSyncAt < 1000) return;
                this.#fire(async () => {
                    if (this.#ready) await this.#ready;
                    if (evt.name !== this.#mapLayer || !this.#enabled) return;
                    this.#processPlacesDebounced();
                });
            }
        });

        // Watch for ext provider elements being added to the DOM, and add hover events.
        this.#linkObserver = new MutationObserver(mutations => {
            mutations.forEach(mutation => {
                for (let idx = 0; idx < mutation.addedNodes.length; idx++) {
                    const nd = mutation.addedNodes[idx];
                    if (nd.nodeType === Node.ELEMENT_NODE) {
                        const $el = $(nd);
                        const $subel = $el.find(GoogleLinkEnhancer.CONFIG.SELECTORS.EXT_PROV_ELEM);
                        if ($el.is(GoogleLinkEnhancer.CONFIG.SELECTORS.EXT_PROV_ELEM)) {
                            this.#addHoverEvent($el);
                            this.#fire(() => this.#formatLinkElements());
                        } else if ($subel.length) {
                            for (let i = 0; i < $subel.length; i++) {
                                this.#addHoverEvent($($subel[i]));
                            }
                            this.#fire(() => this.#formatLinkElements());
                        }
                        if ($el.is(GoogleLinkEnhancer.CONFIG.SELECTORS.EXT_PROV_ELEM_EDIT)) {
                            // Support both production and beta: find any wz-autocomplete
                            const wzAuto = $el.find('wz-autocomplete')[0];
                            if (wzAuto) {
                                // Try to observe shadowRoot if available
                                if (wzAuto.shadowRoot) {
                                    this.#searchResultsObserver.observe(wzAuto.shadowRoot, { childList: true, subtree: true });
                                } else {
                                    // Fallback: try to observe the element itself (may not work if results are in shadow DOM)
                                    this.#searchResultsObserver.observe(wzAuto, { childList: true, subtree: true });
                                    console.warn('GLE: wz-autocomplete has no shadowRoot, observing element directly (beta fallback)');
                                }
                            } else {
                                console.warn('GLE: wz-autocomplete not found in external-provider-edit');
                            }
                        }
                    }
                }
                for (let idx = 0; idx < mutation.removedNodes.length; idx++) {
                    const nd = mutation.removedNodes[idx];
                    if (nd.nodeType === Node.ELEMENT_NODE) {
                        const $el = $(nd);
                        if ($el.is(GoogleLinkEnhancer.CONFIG.SELECTORS.EXT_PROV_ELEM_EDIT)) {
                            this.#searchResultsObserver.disconnect();
                        }
                    }
                }
            });
        });
 
        // Watch for Google place search result list items being added to the DOM
        const that = this;
        this.#searchResultsObserver = new MutationObserver(mutations => {
            mutations.forEach(mutation => {
                for (let idx = 0; idx < mutation.addedNodes.length; idx++) {
                    const nd = mutation.addedNodes[idx];
                    if (nd.nodeType === Node.ELEMENT_NODE && $(nd).is('wz-menu-item.simple-item')) {
                        $(nd).mouseenter(() => {
                            // When mousing over a list item, find the Google place ID from the list that was stored previously.
                            // Then add the point/line to the map.
                            that.#fire(() => that.#addPoint($(nd).attr('item-id')));
                        }).mouseleave(() => {
                            // When leaving the list item, remove the point.
                            that.#destroyPoint();
                        });
                    }
                }
            });
        });
 
        // Watch the side panel for addition of the sidebar-layout div, which indicates a mode change.
        this.#modeObserver = new MutationObserver(mutations => {
            mutations.forEach(mutation => {
                for (let idx = 0; idx < mutation.addedNodes.length; idx++) {
                    const nd = mutation.addedNodes[idx];
                    if (nd.nodeType === Node.ELEMENT_NODE && $(nd).is('.sidebar-layout')) {
                        this.#observeLinks();
                        break;
                    }
                }
            });
        });
 
        // This is a special event that will be triggered when DOM elements are destroyed.
        /* eslint-disable wrap-iife, func-names, object-shorthand */
        (function($) {
            $.event.special.destroyed = {
                remove: function(o) {
                    if (o.handler && o.type !== 'destroyed') {
                        o.handler();
                    }
                }
            };
        })(jQuery);
        /* eslint-enable wrap-iife, func-names, object-shorthand */
 
        // In case a place is already selected on load.
        this.#fire(async () => {
            if (this.#ready) await this.#ready;
            let currentSelection = null;
            try { currentSelection = await this.sdk.Editing.getSelection(); } catch (e) { currentSelection = null; }
            if (currentSelection?.objectType === 'venue' && currentSelection?.ids?.length) {
                await this.#formatLinkElements();
            }
        });
    }

    /**
     * Initialize cache from localStorage
     * @private
     */
    #initCache() {
        const STORED_CACHE = localStorage.getItem(GoogleLinkEnhancer.CONFIG.CACHE.NAME);
        try {
            this.#linkCache = STORED_CACHE ? new Map(Object.entries(JSON.parse(this.#lzString.decompressFromUTF16(STORED_CACHE)))) : new Map();
        } catch (ex) {
            this.#handleError(ex, 'initCache', 'An error occurred while loading the stored cache. A new cache was created.');
            this.#linkCache = new Map();
        }
    }

    /**
     * Error handler for consistent error logging
     * @private
     * @param {Error} error - The error object
     * @param {string} context - Where the error occurred
     * @param {string} [message] - Custom message
     */
    #handleError(error, context, message) {
        const logMessage = message || error.message;
        console.error(`[GoogleLinkEnhancer] ${context}:`, logMessage, error);
    }

    /**
     * Run an async task without letting its rejection escape.
     * In the SDK's async mode every module method returns a Promise, so the places that
     * fire work outside the await-chain (event bus handlers, setTimeout, MutationObserver
     * callbacks, jQuery handlers) would otherwise produce unhandled rejections. This also
     * works with a synchronous SDK, where awaiting a non-thenable is a no-op.
     * @private
     * @param {Function} fn - Task to run.
     * @returns {Promise<void>} Resolves once the task settles.
     */
    #fire(fn) {
        return Promise.resolve()
            .then(() => fn())
            .catch((ex) => this.#handleError(ex, 'fire', 'Unhandled error in async task'));
    }

    /**
     * Debounce function to limit function call frequency
     * @private
     * @param {Function} func - Function to debounce
     * @param {number} wait - Wait time in milliseconds
     * @returns {Function} Debounced function
     */
    #debounce(func, wait) {
        let timeout;
        return (...args) => {
            clearTimeout(timeout);
            // func may be async now, and setTimeout would swallow a rejected Promise.
            timeout = setTimeout(() => this.#fire(() => func.apply(this, args)), wait);
        };
    }
 
    /**
     * Initialize map layer for visual indicators
     * @private
     */
    async #initLayer() {
        // Must stay distinct from PIE's 'SDK Google Link Enhancer' layer, which registers
        // itself as 'Google Link Enhancements'. Both scripts can run at the same time.
        const layerName = GoogleLinkEnhancer.LAYER_NAME;
        const styleContext = {
            strokeColor: (context) => {
                return context?.feature?.properties?.style?.strokeColor;
            },
            strokeWidth: (context) => {
                return context?.feature?.properties?.style?.strokeWidth;
            },
            strokeDashstyle: (context) => {
                return context?.feature?.properties?.style?.strokeDashstyle;
            },
            pointRadius: (context) => {
                return context?.feature?.properties?.style?.pointRadius;
            },
            fillColor: (context) => {
                return context?.feature?.properties?.style?.fillColor;
            },
            strokeOpacity: (context) => {
                return context?.feature?.properties?.style?.strokeOpacity;
            },
            label: (context) => {
                return context?.feature?.properties?.style?.label || '';
            },
            labelYOffset: (context) => {
                return context?.feature?.properties?.style?.labelYOffset || 0;
            },
            fontColor: (context) => {
                return context?.feature?.properties?.style?.fontColor || '#000';
            },
            fontWeight: (context) => {
                return context?.feature?.properties?.style?.fontWeight || 'normal';
            },
            labelOutlineColor: (context) => {
                return context?.feature?.properties?.style?.labelOutlineColor || '';
            },
            labelOutlineWidth: (context) => {
                return context?.feature?.properties?.style?.labelOutlineWidth || 0;
            },
            fontSize: (context) => {
                return context?.feature?.properties?.style?.fontSize || '12';
            }
        };

        const styleRules = [
            {
                style: {
                    strokeColor: '${strokeColor}',
                    strokeWidth: '${strokeWidth}',
                    strokeDashstyle: '${strokeDashstyle}',
                    strokeOpacity: '${strokeOpacity}',
                    pointRadius: '${pointRadius}',
                    fillColor: '${fillColor}',
                    fillOpacity: '0',
                    label: '${label}',
                    labelYOffset: '${labelYOffset}',
                    fontColor: '${fontColor}',
                    fontWeight: '${fontWeight}',
                    labelOutlineColor: '${labelOutlineColor}',
                    labelOutlineWidth: '${labelOutlineWidth}',
                    fontSize: '${fontSize}'
                }
            }
        ];

        this.#mapLayer = layerName;
        try {
            await this.sdk.Map.addLayer({
                layerName: layerName,
                styleContext: styleContext,
                styleRules: styleRules
            });
            await this.sdk.Map.setLayerOpacity({ layerName: layerName, opacity: 0.8 });
            // Must finish before isLayerCheckboxChecked() is used, and it throws
            // InvalidStateError when a userscript re-run registers the same name twice.
            // Start in the enhancer's own state so the Layers tab never shows a checked
            // box for a disabled enhancer (the host script may enable us later).
            await this.sdk.LayerSwitcher.addLayerCheckbox({ name: layerName, isChecked: this.#enabled });
        } catch (ex) {
            this.#handleError(ex, 'initLayer', `Failed to register the ${layerName} layer`);
        }
    }

    /**
     * Mirror the enabled state onto the Layer Switcher checkbox.
     * @private
     * @param {boolean} isChecked - Desired checkbox state.
     */
    async #setLayerCheckboxChecked(isChecked) {
        if (!this.#mapLayer) return;
        try {
            this.#layerCheckboxSyncAt = Date.now();
            await this.sdk.LayerSwitcher.setLayerCheckboxChecked({ name: this.#mapLayer, isChecked: !!isChecked });
        } catch (ex) {
            this.#handleError(ex, 'setLayerCheckboxChecked', 'Failed to update the layer checkbox');
        }
    }

    /**
     * Enable the link enhancer
     * @public
     */
 
    async enable() {
        if (this.#enabled) return;
        // Set the flag first so a second call (or a toggle straight after) cannot double-subscribe.
        this.#enabled = true;
        try {
            // The layer must exist before #processPlaces() reads its Layer Switcher checkbox.
            if (this.#ready) await this.#ready;
            // Keep the Layers tab in step with whoever toggled us on.
            await this.#setLayerCheckboxChecked(true);

            const sidebarContent = $('.edit-area #sidebarContent')[0];
            if (sidebarContent) {
                this.#modeObserver.observe(sidebarContent, { childList: true, subtree: false });
            } else {
                console.warn('[GoogleLinkEnhancer] #sidebarContent not found; mode observer not attached');
            }
            this.#observeLinks();
            // Keep our status tooltips on the provider rows even when PIE writes its
            // name/CID title over them.
            this.#startLinkTitleGuard();
            // Watch for JSONP callbacks. JSONP is used for the autocomplete results when searching for Google links.
            this.#addJsonpInterceptor();
            // Note: Using on() allows passing "this" as a variable, so it can be used in the handler function.
            $('#map').on('mouseenter', null, this, GoogleLinkEnhancer.#onMapMouseenter);
            $(window).on('unload', null, this, GoogleLinkEnhancer.#onWindowUnload);
            // Event listeners are now set up in constructor via SDK Events
            await this.#processPlaces();
            this.#cleanAndSaveLinkCache();
            this.#cacheCleanIntervalID = setInterval(
                () => this.#cleanAndSaveLinkCache(),
                1000 * 60 * GoogleLinkEnhancer.CONFIG.CACHE.CLEAN_INTERVAL_MIN
            );
        } catch (ex) {
            // Callers may not await enable(); a rejection must not escape as unhandled.
            this.#handleError(ex, 'enable', 'Error enabling the link enhancer');
        }
    }

    /**
     * Disable the link enhancer
     * @public
     */
 
    async disable() {
        if (!this.#enabled) return;
        this.#enabled = false;
        try {
            // #mapLayer is only set once #initLayer() has finished.
            if (this.#ready) await this.#ready;
            this.#modeObserver.disconnect();
            this.#linkObserver.disconnect();
            this.#searchResultsObserver.disconnect();
            if (this.#linkTitleObserver) {
                this.#linkTitleObserver.disconnect();
                this.#linkTitleObserver = null;
            }
            // Hand the tooltips back: with the enhancer off, PIE's own texts may stand.
            this.#linkTitles = new WeakMap();
            this.#removeJsonpInterceptor();
            $('#map').off('mouseenter', GoogleLinkEnhancer.#onMapMouseenter);
            $(window).off('unload', null, this, GoogleLinkEnhancer.#onWindowUnload);
            // Event listeners were set up in constructor via SDK Events - no longer need manual cleanup
            if (this.#cacheCleanIntervalID) clearInterval(this.#cacheCleanIntervalID);
            this.#cleanAndSaveLinkCache();
            // Drop the rings straight away and untick the checkbox, so the Layers tab never
            // disagrees with the control that just turned the enhancer off.
            if (this.#mapLayer) {
                await this.sdk.Map.removeAllFeaturesFromLayer({ layerName: this.#mapLayer });
                await this.#setLayerCheckboxChecked(false);
            }
        } catch (ex) {
            this.#handleError(ex, 'disable', 'Error disabling the link enhancer');
        }
    }

    /**
     * Whether the link enhancer is currently enabled.
     * @public
     * @returns {boolean}
     */
    get enabled() {
        return this.#enabled;
    }

    /**
     * Enable or disable the link enhancer. Assignment is fire-and-forget; the async
     * work happens inside enable()/disable(), which handle their own errors.
     * @public
     * @param {boolean} value
     */
    set enabled(value) {
        const next = !!value;
        if (next === this.#enabled) return;
        if (next) {
            void this.enable();
        } else {
            void this.disable();
        }
    }
 
    /**
     * Get the distance limit in meters
     * @public
     * @returns {number} Distance limit
     */
    get distanceLimit() {
        return this.#distanceLimit;
    }

    /**
     * Set the distance limit in meters
     * @public
     * @param {number} value - Distance limit
     */
 
    set distanceLimit(value) {
        this.#distanceLimit = value;
        this.#processPlacesDebounced();
    }

    /**
     * Get whether to show temporarily closed POIs
     * @public
     * @returns {boolean}
     */
    get showTempClosedPOIs() {
        return this.#showTempClosedPOIs;
    }

    /**
     * Set whether to show temporarily closed POIs
     * @public
     * @param {boolean} value
     */
 
    set showTempClosedPOIs(value) {
        this.#showTempClosedPOIs = value;
        this.#processPlacesDebounced();
    }
 
    static #onWindowUnload(evt) {
        evt.data.#cleanAndSaveLinkCache();
    }
 
    /**
     * Clean expired entries and save cache to localStorage
     * @private
     */
    #cleanAndSaveLinkCache() {
        if (!this.#linkCache) return;
        const now = Date.now();
        const maxAge = GoogleLinkEnhancer.CONFIG.CACHE.LIFESPAN_HR * 3600 * 1000;
        
        for (const [id, link] of this.#linkCache.entries()) {
            // Bug fix: normalize location property
            if (link.location) {
                link.loc = link.location;
                delete link.location;
            }
            // Delete link if older than max age
            if (!link.ts || (now - link.ts) > maxAge) {
                this.#linkCache.delete(id);
            }
        }
        
        // Convert Map to object for storage
        const cacheObj = Object.fromEntries(this.#linkCache.entries());
        try {
            localStorage.setItem(
                GoogleLinkEnhancer.CONFIG.CACHE.NAME,
                this.#lzString.compressToUTF16(JSON.stringify(cacheObj))
            );
        } catch (ex) {
            this.#handleError(ex, 'cleanAndSaveLinkCache', 'Failed to save cache to localStorage');
        }
    }
 
    /**
     * Calculate distance between two points in kilometers
     * @private
     * @param {Array} point1 - [lng, lat] coordinates
     * @param {Array} point2 - [lng, lat] coordinates
     * @returns {number} Distance in kilometers
     */
    #distanceBetweenPoints(point1, point2) {
        const ls = this.trf.lineString([point1, point2]);
        const length = this.trf.length(ls);
        return length * 1000; // convert to meters
    }
 
    /**
     * Check if linked Google place is too far from Waze venue
     * @private
     * @param {Object} link - Link info with location
     * @param {Object} venue - Waze venue object
     * @returns {boolean} True if link is too far
     */
    #isLinkTooFar(link, venue) {
        // Validate inputs
        if (!link?.loc || !venue || !venue.geometry || !this.trf) {
            return false;
        }
        
        try {
            const linkPt = [link.loc.lng, link.loc.lat];
            let venuePt;
            let distanceLim = this.distanceLimit;
            
            if (venue.geometry.type === 'Point') {
                venuePt = venue.geometry.coordinates;
            } else if (venue.geometry.type === 'Polygon' || venue.geometry.type === 'MultiPolygon') {
                // Use centroid for polygon venues
                const center = this.trf.centroid(venue.geometry);
                if (!center?.geometry?.coordinates) {
                    return false;
                }
                venuePt = center.geometry.coordinates;
                
                // Add half the bounding box size to account for area coverage
                try {
                    const bbox = this.trf.bbox(venue.geometry);
                    if (bbox && bbox.length >= 4) {
                        // bbox is [minLng, minLat, maxLng, maxLat]
                        const farCorner = [bbox[2], bbox[3]]; // top-right corner
                        distanceLim += this.#distanceBetweenPoints(venuePt, farCorner) / 2;
                    }
                } catch (e) {
                    // If bbox fails, just use centroid distance
                    console.warn('[GoogleLinkEnhancer] Error calculating bbox:', e);
                }
            } else {
                return false;
            }
            
            if (!venuePt || venuePt.length !== 2) {
                return false;
            }
            
            const distance = this.#distanceBetweenPoints(linkPt, venuePt);
            return distance > distanceLim;
        } catch (ex) {
            this.#handleError(ex, 'isLinkTooFar', 'Error checking distance');
            return false;
        }
    }
 
    /**
     * Process all places and add visual indicators for issues
     * @private
     */
    async #processPlaces() {
        try {
            if (!this.#enabled) return;
            
            // The layer and its Layer Switcher checkbox are registered asynchronously by
            // #initLayer(); isLayerCheckboxChecked() throws InvalidStateError until then.
            if (this.#ready) await this.#ready;

            let layerVisible = true;
            try {
                layerVisible = (await this.sdk.LayerSwitcher.isLayerCheckboxChecked({ name: this.#mapLayer })) !== false;
            } catch (ex) {
                // Checkbox missing (registration failed) — keep drawing instead of nothing.
                this.#handleError(ex, 'processPlaces.layerVisible', 'Could not read the layer checkbox state');
            }

            const existingLinks = await GoogleLinkEnhancer.#getExistingLinks(this.sdk);
            await this.sdk.Map.removeAllFeaturesFromLayer({ layerName: this.#mapLayer });
            const drawnLinks = [];
            
            const venues = (await this.sdk.DataModel.Venues.getAll()) || [];
            venues.forEach(venue => {
                const venueId = venue.id;
                const promises = [];
                
                for (const provID of (venue.externalProviderIds || [])) {
                    const id = provID;

                    // Check for duplicate links
                    const linkInfo = existingLinks[id];
                    if (linkInfo?.count > 1) {
                        const geometry = venue.geometry;
                        if (!geometry) return;
                        
                        const width = geometry.type === 'Point' ? 4 : 12;
                        const color = '#fb8d00';
                        const features = [];
                        
                        try {
                            const venueFeature = geometry.type === 'Point'
                                ? this.trf.point(geometry.coordinates, {
                                    styleName: 'venueStyle',
                                    style: { strokeWidth: width, strokeColor: color, pointRadius: 15 }
                                }, { id: `venue_${venue.id}` })
                                : this.trf.polygon(geometry.coordinates, {
                                    styleName: 'venueStyle',
                                    style: { strokeColor: color, strokeWidth: width }
                                }, { id: `polyvenue_${venue.id}` });
                            features.push(venueFeature);
                            
                            const lineStart = this.trf.centroid(geometry);
                            if (lineStart?.geometry?.coordinates) {
                                for (const linkVenue of linkInfo.venues) {
                                    if (linkVenue?.geometry && linkVenue !== venue && 
                                        !drawnLinks.some(dl => (dl[0] === venue && dl[1] === linkVenue) || (dl[0] === linkVenue && dl[1] === venue))) {
                                        const endPoint = this.trf.centroid(linkVenue.geometry);
                                        if (endPoint?.geometry?.coordinates) {
                                            features.push(this.trf.lineString(
                                                [lineStart.geometry.coordinates, endPoint.geometry.coordinates],
                                                { styleName: 'lineStyle', style: { strokeWidth: 4, strokeColor: color, strokeDashstyle: '12 12' } },
                                                { id: `ls_${lineStart.geometry.toString()}_${endPoint.geometry.toString()}` }
                                            ));
                                            drawnLinks.push([venue, linkVenue]);
                                        }
                                    }
                                }
                            }
                            
                            if (layerVisible && features.length > 0) {
                                this.#fire(() => this.sdk.Map.addFeaturesToLayer({ features: features, layerName: this.#mapLayer }));
                            }
                        } catch (ex) {
                            this.#handleError(ex, 'processPlaces.duplicateLinks', 'Error processing duplicate links');
                        }
                    }
                    
                    promises.push(this.#getLinkInfoAsync(id));
                }

                // Process all results of link lookups and add a highlight feature if needed
                Promise.all(promises).then(async results => {
                    // Re-fetch the venue to ensure we have the current state
                    const currentVenue = await this.sdk.DataModel.Venues.getById({ venueId });
                    if (!currentVenue || !currentVenue.geometry) {
                        return; // Venue was deleted
                    }
                    
                    let strokeColor = null;
                    let strokeDashStyle = 'solid';
                    const closedNamePattern = /^(\[|\()?(permanently |temporarily )?closed(\]|\)| -)|( \(|- |\[)(permanently |temporarily )?closed(\)|\])?$/i;
                    
                    if (!this.#DISABLE_CLOSED_PLACES && results.some(res => res.permclosed)) {
                        if (closedNamePattern.test(currentVenue.name)) {
                            strokeDashStyle = currentVenue.geometry.type === 'Point' ? '2 6' : '2 16';
                        }
                        strokeColor = '#F00';
                    } else if (results.some(res => this.#isLinkTooFar(res, currentVenue))) {
                        strokeColor = '#0FF';
                    } else if (!this.#DISABLE_CLOSED_PLACES && this.#showTempClosedPOIs && results.some(res => res.tempclosed)) {
                        if (closedNamePattern.test(currentVenue.name)) {
                            strokeDashStyle = currentVenue.geometry.type === 'Point' ? '2 6' : '2 16';
                        }
                        strokeColor = '#FD3';
                    } else if (results.some(res => res.notFound)) {
                        strokeColor = '#F0F';
                    }
                    
                    if (strokeColor && layerVisible) {
                        const style = {
                            strokeWidth: currentVenue.geometry.type === 'Point' ? 4 : 12,
                            strokeColor,
                            strokeDashStyle,
                            pointRadius: 15
                        };
                        const feature = currentVenue.geometry.type === 'Point'
                            ? this.trf.point(currentVenue.geometry.coordinates, { styleName: 'placeStyle', style: style }, { id: `place_${currentVenue.id}` })
                            : this.trf.polygon(currentVenue.geometry.coordinates, { styleName: 'placeStyle', style: style }, { id: `place_${currentVenue.id}` });
                        await this.sdk.Map.addFeaturesToLayer({ features: [feature], layerName: this.#mapLayer });
                    }
                }).catch(ex => {
                    this.#handleError(ex, 'processPlaces.Promise', 'Error processing venue links');
                });
            });
        } catch (ex) {
            this.#handleError(ex, 'processPlaces', 'Error in processPlaces');
        }
    }
 
    /**
     * Cache a link with timestamp
     * @private
     * @param {string} id - Place ID
     * @param {Object} link - Link information
     */
    #cacheLink(id, link) {
        link.ts = Date.now();
        this.#linkCache.set(id, link);
        
        // Enforce max cache size
        if (this.#linkCache.size > GoogleLinkEnhancer.CONFIG.CACHE.MAX_SIZE) {
            const firstKey = this.#linkCache.keys().next().value;
            this.#linkCache.delete(firstKey);
        }
    }
 
    /**
     * Get link information from cache or Google Places API
     * @private
     * @param {string} placeId - Google Place ID
     * @returns {Promise<Object>} Link information
     */
    #getLinkInfoAsync(placeId) {
        return new Promise(resolve => {
            let link = this.#linkCache.get(placeId);
            if (!link) {
                const request = {
                    placeId,
                    fields: ['geometry', 'business_status']
                };
                this.#placesService.getDetails(request, (place, requestStatus) => {
                    link = {};
                    if (requestStatus === google.maps.places.PlacesServiceStatus.OK) {
                        const loc = place.geometry.location;
                        link.loc = { lng: loc.lng(), lat: loc.lat() };
                        if (place.business_status === 'CLOSED_PERMANENTLY') {
                            link.permclosed = true;
                        } else if (place.business_status === 'CLOSED_TEMPORARILY') {
                            link.tempclosed = true;
                        }
                        this.#cacheLink(placeId, link);
                    } else if (requestStatus === google.maps.places.PlacesServiceStatus.NOT_FOUND) {
                        link.notfound = true;
                        this.#cacheLink(placeId, link);
                    } else if (this.#disableApiUntil) {
                        link.apiDisabled = true;
                    } else {
                        link.error = requestStatus;
                        this.#disableApiUntil = Date.now() + GoogleLinkEnhancer.CONFIG.DEFAULTS.API_DISABLE_DURATION;
                        this.#handleError(
                            new Error(requestStatus),
                            'getLinkInfoAsync',
                            `API temporarily disabled due to error: ${requestStatus}`
                        );
                    }
                    resolve(link);
                });
            } else {
                resolve(link);
            }
        });
    }
 
    static #onMapMouseenter(event) {
        // If the point isn't destroyed yet, destroy it when mousing over the map.
        event.data.#destroyPoint();
    }
 
    /**
     * Format and colorize link elements in edit panel
     * @private
     * @param {number} [callCount=0] - Retry counter
     */
    async #formatLinkElements(callCount = 0) {
        try {
            const editPanel = document.getElementById('edit-panel');
            if (!editPanel) return;
            
            const links = editPanel.querySelectorAll(GoogleLinkEnhancer.CONFIG.SELECTORS.EXT_PROV_ELEM);

            // Resolve the selected venue once: every SDK read is a Promise in async mode,
            // and the per-element lookups below all re-fetched the same venue.
            let selection;
            try { selection = await this.sdk.Editing.getSelection(); } catch (e) { selection = null; }
            const venue = selection?.objectType === 'venue' && selection?.ids?.length
                ? await this.sdk.DataModel.Venues.getById({ venueId: selection.ids[0] })
                : null;
            
            if (!links.length) {
                // Retry if links aren't available yet
                if (callCount < GoogleLinkEnhancer.CONFIG.DEFAULTS.MAX_RETRY_CALLS 
                    && venue) {
                    setTimeout(
                        () => this.#fire(() => this.#formatLinkElements(++callCount)),
                        GoogleLinkEnhancer.CONFIG.DEFAULTS.RETRY_INTERVAL
                    );
                }
            } else {
                const existingLinks = await GoogleLinkEnhancer.#getExistingLinks(this.sdk);

                // Fetch all links first
                const promises = [];
                const extProvElements = [];
                
                links.forEach(linkEl => {
                    const $linkEl = $(linkEl);
                    extProvElements.push($linkEl);

                    const id = this.#providerIdAt($linkEl, venue);
                    if (!id) return;

                    promises.push(this.#getLinkInfoAsync(id));
                });
                
                await Promise.all(promises);

                extProvElements.forEach($extProvElem => {
                    const id = this.#providerIdAt($extProvElem, venue);
                    if (!id) return;

                    const contentQuery = GoogleLinkEnhancer.CONFIG.SELECTORS.EXT_PROV_ELEM_CONTENT;
                    const link = this.#linkCache.get(id);
                    const $content = $extProvElem.find(contentQuery);
                    
                    if (existingLinks[id]?.count > 1 && existingLinks[id].isThisVenue) {
                        setTimeout(() => {
                            $content.css({ backgroundColor: GoogleLinkEnhancer.CONFIG.COLORS.HIGHLIGHT_BG_ORANGE });
                            this.#applyLinkTitle($content, this.strings.linkedToXPlaces.replace('{0}', existingLinks[id].count));
                        }, 50);
                    }
                    
                    this.#addHoverEvent($extProvElem, venue);
                    
                    if (link) {
                        if (link.permclosed && !this.#DISABLE_CLOSED_PLACES) {
                            $content.css({ backgroundColor: GoogleLinkEnhancer.CONFIG.COLORS.HIGHLIGHT_BG_RED });
                            this.#applyLinkTitle($content, this.strings.permClosedPlace);
                        } else if (link.tempclosed && !this.#DISABLE_CLOSED_PLACES) {
                            $content.css({ backgroundColor: GoogleLinkEnhancer.CONFIG.COLORS.HIGHLIGHT_BG_YELLOW });
                            this.#applyLinkTitle($content, this.strings.tempClosedPlace);
                        } else if (link.notFound) {
                            $content.css({ backgroundColor: GoogleLinkEnhancer.CONFIG.COLORS.NOT_FOUND });
                            this.#applyLinkTitle($content, this.strings.badLink);
                        } else {
                            if (venue && this.#isLinkTooFar(link, venue)) {
                                $content.css({ backgroundColor: GoogleLinkEnhancer.CONFIG.COLORS.HIGHLIGHT_BG_CYAN });
                                this.#applyLinkTitle($content, this.strings.tooFar.replace('{0}', this.distanceLimit));
                            } else {
                                // Reset in case we just deleted another provider
                                $content.css({ backgroundColor: '' });
                                this.#applyLinkTitle($content, '');
                            }
                        }
                    }
                });
            }
        } catch (ex) {
            this.#handleError(ex, 'formatLinkElements', 'Error formatting link elements');
        }
    }

    /**
     * Set (or clear) the status tooltip on an external provider row and remember it, so it
     * can be put back if something else overwrites it.
     *
     * This is not theoretical: PIE's "Show external provider tooltip" feature runs
     * `_applyExtProviderTitles()`, which writes `<provider name>\nCID: <cid>` unless
     * `settings.EnableGLE` is true. POI Shortcuts switches PIE's GLE off while its own is
     * active, so PIE ends up stamping its plain name/CID text over the closed / invalid /
     * too-far message. Removing the GLE must not cost us the status tooltip.
     * @private
     * @param {jQuery} $content - The div.external-provider-content element.
     * @param {string} title - Tooltip text; empty to clear it.
     */
    #applyLinkTitle($content, title) {
        const el = $content && $content[0];
        if (!el) return;
        if (title) {
            this.#linkTitles.set(el, title);
            if (el.getAttribute('title') !== title) el.setAttribute('title', title);
        } else {
            this.#linkTitles.delete(el);
            if (el.getAttribute('title') !== null) el.removeAttribute('title');
        }
    }

    /**
     * Re-assert our status tooltips if another script (or WME) rewrites the title
     * attribute on a row we have already labelled.
     * @private
     */
    #startLinkTitleGuard() {
        if (this.#linkTitleObserver) return;
        this.#linkTitleObserver = new MutationObserver((records) => {
            for (const record of records) {
                const el = record.target;
                const desired = this.#linkTitles.get(el);
                if (!desired) continue;
                if (el.getAttribute('title') !== desired) el.setAttribute('title', desired);
            }
        });
        // #edit-panel is recreated by WME; observing from <body> keeps the guard attached.
        this.#linkTitleObserver.observe(document.body, {
            attributes: true,
            attributeFilter: ['title'],
            subtree: true
        });
    }
 
    /**
     * Get all existing Google links across all venues
     * @private
     * @static
     * @returns {Promise<Object>} Map of place IDs to link info
     */
    static async #getExistingLinks(sdk) {
        const existingLinks = {};
        let thisVenue;
        try { thisVenue = await sdk.Editing.getSelection(); } catch (e) { return {}; }
        if (thisVenue?.objectType !== 'venue' || !thisVenue?.ids?.length) return {};
        
        const thisVenueId = thisVenue.ids[0];
        let venues = [];
        try { venues = (await sdk.DataModel.Venues.getAll()) || []; } catch (ex) { return {}; }
        for (const venue of venues) {
            const isThisVenue = venue.id === thisVenueId;
            const thisPlaceIDs = [];
            for (const provID of (venue.externalProviderIds || [])) {
                const id = provID;
                if (!thisPlaceIDs.includes(id)) {
                    thisPlaceIDs.push(id);
                    let link = existingLinks[id];
                    if (link) {
                        link.count++;
                        link.venues.push(venue);
                    } else {
                        link = { count: 1, venues: [venue] };
                        existingLinks[id] = link;
                    }
                    link.isThisVenue = link.isThisVenue || isThisVenue;
                }
            }
        }
        return existingLinks;
    }
 
    /**
     * Remove the POI point from the map
     * @private
     */
    #destroyPoint() {
        // Invalidate any #addPoint still awaiting SDK reads. Without this a mouseleave that
        // arrives mid-flight finds no features yet, does nothing, and the point the pending
        // call adds afterwards stays on the map forever.
        this.#hoverSeq++;
        const featureIds = [this.#ptFeature?.id, this.#lineFeature?.id].filter(Boolean);
        this.#ptFeature = null;
        this.#lineFeature = null;
        if (this.#timeoutID) {
            clearTimeout(this.#timeoutID);
            this.#timeoutID = null;
        }
        if (featureIds.length === 0) return;
        // Fire-and-forget: the SDK call returns a Promise in async mode.
        this.#fire(() => this.sdk.Map.removeFeaturesFromLayer({ featureIds, layerName: this.#mapLayer }));
    }
 
    /**
     * Get the current map extent
     * @private
     * @returns {Array} BBox [minX, minY, maxX, maxY]
     */
    async #getOLMapExtent() {
        return await this.sdk.Map.getMapExtent();
    }
 
    /**
     * Add a point and line to the map showing Google place location and distance
     * @private
     * @param {string} id - Google Place ID
     * @param {Object} [venue] - Already-resolved venue (skips an SDK round-trip)
     */
    async #addPoint(id, venue) {
        if (!id) return;
        const seq = ++this.#hoverSeq;
        const link = await this.#getLinkInfoAsync(id);
        if (seq !== this.#hoverSeq) return;
        if (link && !link.notFound) {
            const coord = link.loc;
            const poiPt = this.trf.point([coord.lng, coord.lat]);
            
            let currentVenue = venue;
            if (!currentVenue) {
                let selection;
                try { selection = await this.sdk.Editing.getSelection(); } catch (e) { selection = null; }
                if (!selection || selection.objectType !== 'venue' || !selection.ids?.length) return;
                currentVenue = await this.sdk.DataModel.Venues.getById({ venueId: selection.ids[0] });
            }
            
            if (!currentVenue || seq !== this.#hoverSeq) return;
            
            const placeGeom = this.trf.centroid(currentVenue.geometry).geometry;
            const placePt = this.trf.point(placeGeom.coordinates);
            
            const ext = await this.#getOLMapExtent();
            const lsBounds = this.trf.lineString([
                [ext[0], ext[3]],
                [ext[0], ext[1]],
                [ext[2], ext[1]],
                [ext[2], ext[3]],
                [ext[0], ext[3]]
            ]);
            
            let lsLine = this.trf.lineString([placePt.geometry.coordinates, poiPt.geometry.coordinates]);
            
            // Calculate distance before line split
            let distance = this.#distanceBetweenPoints(poiPt.geometry.coordinates, placePt.geometry.coordinates);
            let label = '';
            
            // Format distance label based on settings
            let unitConversion;
            let unit1;
            let unit2;
            
            let isImperial = false;
            try { isImperial = !!(await this.sdk.Settings.getUserSettings()).isImperial; } catch (e) { isImperial = false; }
            if (seq !== this.#hoverSeq) return;
            if (isImperial) {
                distance *= 3.28084;
                unitConversion = 5280;
                unit1 = ' ft';
                unit2 = ' mi';
            } else {
                unitConversion = 1000;
                unit1 = ' m';
                unit2 = ' km';
            }
            
            if (distance > unitConversion * 10) {
                label = Math.round(distance / unitConversion) + unit2;
            } else if (distance > 1000) {
                label = (Math.round(distance / (unitConversion / 10)) / 10) + unit2;
            } else {
                label = Math.round(distance) + unit1;
            }
            
            // If the line extends outside the bounds, split it so we don't draw a line across the world.
            try {
                const splits = this.trf.lineSplit(lsLine, lsBounds);
                if (splits && splits.features.length > 0) {
                    for (const split of splits.features) {
                        if (split.geometry && split.geometry.coordinates && split.geometry.coordinates.length >= 2) {
                            // Use the first split feature that connects venue to POI
                            lsLine = split;
                            break;
                        }
                    }
                }
            } catch (ex) {
                console.warn('[GoogleLinkEnhancer] Error splitting line:', ex);
                // Continue with unsplit line if split fails
            }
            
            // Drop the previous point without invalidating this call (#destroyPoint would
            // bump the sequence).
            const staleIds = [this.#ptFeature?.id, this.#lineFeature?.id].filter(Boolean);
            this.#ptFeature = null;
            this.#lineFeature = null;
            if (staleIds.length > 0) {
                this.#fire(() => this.sdk.Map.removeFeaturesFromLayer({ featureIds: staleIds, layerName: this.#mapLayer }));
            }
            this.#ptFeature = this.trf.point(poiPt.geometry.coordinates, {
                styleName: 'googlePlacePointStyle',
                style: {
                    pointRadius: 6,
                    strokeWidth: 30,
                    strokeColor: '#FF0',
                    fillColor: '#FF0',
                    strokeOpacity: 0.5
                }
            }, { id: `PoiPT_${poiPt.toString()}` });
            
            this.#lineFeature = this.trf.lineString(lsLine.geometry.coordinates, {
                styleName: 'googlePlaceLineStyle',
                style: {
                    strokeWidth: 3,
                    strokeDashstyle: '12 8',
                    strokeColor: '#FF0',
                    label,
                    labelYOffset: 45,
                    fontColor: '#FF0',
                    fontWeight: 'bold',
                    labelOutlineColor: '#000',
                    labelOutlineWidth: 4,
                    fontSize: '18'
                }
            }, { id: `LsLine_${lsLine.toString()}` });
            
            const ptFeature = this.#ptFeature;
            const lineFeature = this.#lineFeature;
            await this.sdk.Map.addFeaturesToLayer({ features: [ptFeature, lineFeature], layerName: this.#mapLayer });
            // A mouseleave (or a newer hover) may have won while we were adding: take the
            // features back off instead of leaving them on the map.
            if (seq !== this.#hoverSeq) {
                this.#ptFeature = null;
                this.#lineFeature = null;
                this.#fire(() => this.sdk.Map.removeFeaturesFromLayer({
                    featureIds: [ptFeature.id, lineFeature.id],
                    layerName: this.#mapLayer
                }));
                return;
            }
            this.#timeoutDestroyPoint();
        }
    }
 
    /**
     * Destroy the point after timeout
     * @private
     */
    #timeoutDestroyPoint() {
        if (this.#timeoutID) clearTimeout(this.#timeoutID);
        this.#timeoutID = setTimeout(
            () => this.#destroyPoint(),
            GoogleLinkEnhancer.CONFIG.DEFAULTS.POINT_TIMEOUT
        );
    }
 
    /**
     * Place id for a link element, given an already-resolved venue.
     * Synchronous on purpose: a link element's position maps 1:1 to externalProviderIds,
     * so no SDK read is needed once the venue is known — which keeps the formatting loops
     * synchronous while all venue access is awaited once per pass.
     * @private
     * @param {jQuery} $el - jQuery element
     * @param {Object|null} venue - Venue read from the SDK
     * @returns {string|null} Place ID or null
     */
    #providerIdAt($el, venue) {
        const providerIndex = $el.parent().children().toArray().indexOf($el[0]);
        return venue?.externalProviderIds?.[providerIndex] ?? null;
    }

    /**
     * Get Place ID from DOM element, resolving the selected venue when not supplied.
     * @private
     * @param {jQuery} $el - jQuery element
     * @param {Object} [venue] - Already-resolved venue
     * @returns {Promise<string|null>} Place ID or null
     */
    async #getIdFromElement($el, venue) {
        let currentVenue = venue;
        if (!currentVenue) {
            let selection;
            try { selection = await this.sdk.Editing.getSelection(); } catch (e) { return null; }
            if (!selection || selection.objectType !== 'venue' || !selection.ids?.length) return null;
            currentVenue = await this.sdk.DataModel.Venues.getById({ venueId: selection.ids[0] });
        }
        return this.#providerIdAt($el, currentVenue);
    }
 
    /**
     * Add hover event to show point on map
     * @private
     * @param {jQuery} $el - jQuery element
     */
    #addHoverEvent($el, venue) {
        // Re-bind only our own handlers: #formatLinkElements runs on every DOM mutation, and
        // stacking a new hover pair each time made N #addPoint calls race per mouseenter.
        $el.off('.gleHover');
        $el.on('mouseenter.gleHover', () => this.#fire(async () => {
            // getIdFromElement is async in async mode, so it cannot be passed straight
            // into addPoint as an id.
            const id = await this.#getIdFromElement($el, venue);
            if (id) await this.#addPoint(id, venue);
        }));
        $el.on('mouseleave.gleHover', () => this.#destroyPoint());
    }
 
    /**
     * Start observing edit panel for link elements
     * @private
     */
    #observeLinks() {
        const editPanel = document.querySelector('#edit-panel');
        if (!editPanel) {
            setTimeout(() => this.#observeLinks(), 250);
            return;
        }
        this.editPanelElem = editPanel;
        this.#linkObserver.observe(editPanel, { childList: true, subtree: true });
    }
 
    /**
     * Intercept JSONP callbacks to process Google autocomplete results
     * Watches for JSONP script tags added to the DOM and overrides their callbacks
     * to extract place IDs from search results.
     * @private
     */
    #addJsonpInterceptor() {
        // The idea for this function was hatched here:
        // https://stackoverflow.com/questions/6803521/can-google-maps-places-autocomplete-api-be-used-via-ajax/9856786
 
        // The head element, where the Google Autocomplete code will insert a tag
        // for a javascript file.
        const head = $('head')[0];
        // The name of the method the Autocomplete code uses to insert the tag.
        const method = 'appendChild';
        // The method we will be overriding.
        const originalMethod = head[method];
        this.#originalHeadAppendChildMethod = originalMethod;
        const that = this;
        /* eslint-disable func-names, prefer-rest-params */ // Doesn't work as an arrow function (at least not without some modifications)
        head[method] = function() {
            // Check that the element is a javascript tag being inserted by Google.
            if (arguments[0] && arguments[0].src && arguments[0].src.match(/GetPredictions/)) {
                // Regex to extract the name of the callback method that the JSONP will call.
                const callbackMatchObject = (/callback=([^&]+)&|$/).exec(arguments[0].src);
 
                // Regex to extract the search term that was entered by the user.
                const searchTermMatchObject = (/\?1s([^&]+)&/).exec(arguments[0].src);
 
                // const searchTerm = unescape(searchTermMatchObject[1]);
                if (callbackMatchObject && searchTermMatchObject) {
                    // The JSONP callback method is in the form "abc.def" and each time has a different random name.
                    const names = callbackMatchObject[1].split('.');
                    // Store the original callback method.
                    const originalCallback = names[0] && names[1] && window[names[0]] && window[names[0]][names[1]];
 
                    if (originalCallback) {
                        const newCallback = function() { // Define your own JSONP callback
                            if (arguments[0] && arguments[0].predictions) {
                                // SUCCESS!
 
                                // The autocomplete results
                                const data = arguments[0];
 
                                // console.log('GLE: ' + JSON.stringify(data));
                                that._lastSearchResultPlaceIds = data.predictions.map(pred => pred.place_id);
 
                                // Call the original callback so the WME dropdown can do its thing.
                                originalCallback(data);
                            }
                        };
 
                        // Add copy of all the attributes of the old callback function to the new callback function.
                        // This prevents the autocomplete functionality from throwing an error.
                        Object.keys(originalCallback).forEach(key => {
                            newCallback[key] = originalCallback[key];
                        });
                        window[names[0]][names[1]] = newCallback; // Override the JSONP callback
                    }
                }
            }
            // Insert the element into the dom, regardless of whether it was being inserted by Google.
            return originalMethod.apply(this, arguments);
        };
        /* eslint-enable func-names, prefer-rest-params */
    }
 
    /**
     * Remove JSONP interceptor
     * @private
     */
    #removeJsonpInterceptor() {
        $('head')[0].appendChild = this.#originalHeadAppendChildMethod;
    }
 
    /**
     * Initialize LZ-String compression library
     * Used for compressing cache data stored in localStorage
     * @private
     */
    #initLZString() {
        /* eslint-disable */ // Disabling eslint since this is copied third-party code
        // LZ Compressor
        // Copyright (c) 2013 Pieroxy <pieroxy@pieroxy.net>
        // This work is free. You can redistribute it and/or modify it
        // under the terms of the WTFPL, Version 2
        // LZ-based compression algorithm, version 1.4.4
        this.#lzString = (function () {
            // private property
            const f = String.fromCharCode;
            const keyStrBase64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=";
            const keyStrUriSafe = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+-$";
            const baseReverseDic = {};
 
            function getBaseValue(alphabet, character) {
                if (!baseReverseDic[alphabet]) {
                    baseReverseDic[alphabet] = {};
                    for (let i = 0; i < alphabet.length; i++) {
                        baseReverseDic[alphabet][alphabet.charAt(i)] = i;
                    }
                }
                return baseReverseDic[alphabet][character];
            }
            var LZString = {
                compressToBase64: function (input) {
                    if (input === null) return "";
                    const res = LZString._compress(input, 6, function (a) {
                        return keyStrBase64.charAt(a);
                    });
                    switch (res.length % 4) { // To produce valid Base64
                        default: // When could this happen ?
                        case 0:
                            return res;
                        case 1:
                            return res + "===";
                        case 2:
                            return res + "==";
                        case 3:
                            return res + "=";
                    }
                },
                decompressFromBase64: function (input) {
                    if (input === null) return "";
                    if (input === "") return null;
                    return LZString._decompress(input.length, 32, function (index) {
                        return getBaseValue(keyStrBase64, input.charAt(index));
                    });
                },
                compressToUTF16: function (input) {
                    if (input === null) return "";
                    return LZString._compress(input, 15, function (a) {
                        return f(a + 32);
                    }) + " ";
                },
                decompressFromUTF16: function (compressed) {
                    if (compressed === null) return "";
                    if (compressed === "") return null;
                    return LZString._decompress(compressed.length, 16384, function (index) {
                        return compressed.charCodeAt(index) - 32;
                    });
                },
 
                compress: function (uncompressed) {
                    return LZString._compress(uncompressed, 16, function (a) {
                        return f(a);
                    });
                },
                _compress: function (uncompressed, bitsPerChar, getCharFromInt) {
                    if (uncompressed === null) return "";
                    let i, value,
                        context_dictionary = {},
                        context_dictionaryToCreate = {},
                        context_c = "",
                        context_wc = "",
                        context_w = "",
                        context_enlargeIn = 2, // Compensate for the first entry which should not count
                        context_dictSize = 3,
                        context_numBits = 2,
                        context_data = [],
                        context_data_val = 0,
                        context_data_position = 0,
                        ii;
                    for (ii = 0; ii < uncompressed.length; ii += 1) {
                        context_c = uncompressed.charAt(ii);
                        if (!Object.prototype.hasOwnProperty.call(context_dictionary, context_c)) {
                            context_dictionary[context_c] = context_dictSize++;
                            context_dictionaryToCreate[context_c] = true;
                        }
                        context_wc = context_w + context_c;
                        if (Object.prototype.hasOwnProperty.call(context_dictionary, context_wc)) {
                            context_w = context_wc;
                        } else {
                            if (Object.prototype.hasOwnProperty.call(context_dictionaryToCreate, context_w)) {
                                if (context_w.charCodeAt(0) < 256) {
                                    for (i = 0; i < context_numBits; i++) {
                                        context_data_val = (context_data_val << 1);
                                        if (context_data_position === bitsPerChar - 1) {
                                            context_data_position = 0;
                                            context_data.push(getCharFromInt(context_data_val));
                                            context_data_val = 0;
                                        } else {
                                            context_data_position++;
                                        }
                                    }
                                    value = context_w.charCodeAt(0);
                                    for (i = 0; i < 8; i++) {
                                        context_data_val = (context_data_val << 1) | (value & 1);
                                        if (context_data_position === bitsPerChar - 1) {
                                            context_data_position = 0;
                                            context_data.push(getCharFromInt(context_data_val));
                                            context_data_val = 0;
                                        } else {
                                            context_data_position++;
                                        }
                                        value = value >> 1;
                                    }
                                } else {
                                    value = 1;
                                    for (i = 0; i < context_numBits; i++) {
                                        context_data_val = (context_data_val << 1) | value;
                                        if (context_data_position === bitsPerChar - 1) {
                                            context_data_position = 0;
                                            context_data.push(getCharFromInt(context_data_val));
                                            context_data_val = 0;
                                        } else {
                                            context_data_position++;
                                        }
                                        value = 0;
                                    }
                                    value = context_w.charCodeAt(0);
                                    for (i = 0; i < 16; i++) {
                                        context_data_val = (context_data_val << 1) | (value & 1);
                                        if (context_data_position === bitsPerChar - 1) {
                                            context_data_position = 0;
                                            context_data.push(getCharFromInt(context_data_val));
                                            context_data_val = 0;
                                        } else {
                                            context_data_position++;
                                        }
                                        value = value >> 1;
                                    }
                                }
                                context_enlargeIn--;
                                if (context_enlargeIn === 0) {
                                    context_enlargeIn = Math.pow(2, context_numBits);
                                    context_numBits++;
                                }
                                delete context_dictionaryToCreate[context_w];
                            } else {
                                value = context_dictionary[context_w];
                                for (i = 0; i < context_numBits; i++) {
                                    context_data_val = (context_data_val << 1) | (value & 1);
                                    if (context_data_position === bitsPerChar - 1) {
                                        context_data_position = 0;
                                        context_data.push(getCharFromInt(context_data_val));
                                        context_data_val = 0;
                                    } else {
                                        context_data_position++;
                                    }
                                    value = value >> 1;
                                }
                            }
                            context_enlargeIn--;
                            if (context_enlargeIn === 0) {
                                context_enlargeIn = Math.pow(2, context_numBits);
                                context_numBits++;
                            }
                            // Add wc to the dictionary.
                            context_dictionary[context_wc] = context_dictSize++;
                            context_w = String(context_c);
                        }
                    }
                    // Output the code for w.
                    if (context_w !== "") {
                        if (Object.prototype.hasOwnProperty.call(context_dictionaryToCreate, context_w)) {
                            if (context_w.charCodeAt(0) < 256) {
                                for (i = 0; i < context_numBits; i++) {
                                    context_data_val = (context_data_val << 1);
                                    if (context_data_position === bitsPerChar - 1) {
                                        context_data_position = 0;
                                        context_data.push(getCharFromInt(context_data_val));
                                        context_data_val = 0;
                                    } else {
                                        context_data_position++;
                                    }
                                }
                                value = context_w.charCodeAt(0);
                                for (i = 0; i < 8; i++) {
                                    context_data_val = (context_data_val << 1) | (value & 1);
                                    if (context_data_position === bitsPerChar - 1) {
                                        context_data_position = 0;
                                        context_data.push(getCharFromInt(context_data_val));
                                        context_data_val = 0;
                                    } else {
                                        context_data_position++;
                                    }
                                    value = value >> 1;
                                }
                            } else {
                                value = 1;
                                for (i = 0; i < context_numBits; i++) {
                                    context_data_val = (context_data_val << 1) | value;
                                    if (context_data_position === bitsPerChar - 1) {
                                        context_data_position = 0;
                                        context_data.push(getCharFromInt(context_data_val));
                                        context_data_val = 0;
                                    } else {
                                        context_data_position++;
                                    }
                                    value = 0;
                                }
                                value = context_w.charCodeAt(0);
                                for (i = 0; i < 16; i++) {
                                    context_data_val = (context_data_val << 1) | (value & 1);
                                    if (context_data_position === bitsPerChar - 1) {
                                        context_data_position = 0;
                                        context_data.push(getCharFromInt(context_data_val));
                                        context_data_val = 0;
                                    } else {
                                        context_data_position++;
                                    }
                                    value = value >> 1;
                                }
                            }
                            context_enlargeIn--;
                            if (context_enlargeIn === 0) {
                                context_enlargeIn = Math.pow(2, context_numBits);
                                context_numBits++;
                            }
                            delete context_dictionaryToCreate[context_w];
                        } else {
                            value = context_dictionary[context_w];
                            for (i = 0; i < context_numBits; i++) {
                                context_data_val = (context_data_val << 1) | (value & 1);
                                if (context_data_position === bitsPerChar - 1) {
                                    context_data_position = 0;
                                    context_data.push(getCharFromInt(context_data_val));
                                    context_data_val = 0;
                                } else {
                                    context_data_position++;
                                }
                                value = value >> 1;
                            }
                        }
                        context_enlargeIn--;
                        if (context_enlargeIn === 0) {
                            context_enlargeIn = Math.pow(2, context_numBits);
                            context_numBits++;
                        }
                    }
                    // Mark the end of the stream
                    value = 2;
                    for (i = 0; i < context_numBits; i++) {
                        context_data_val = (context_data_val << 1) | (value & 1);
                        if (context_data_position === bitsPerChar - 1) {
                            context_data_position = 0;
                            context_data.push(getCharFromInt(context_data_val));
                            context_data_val = 0;
                        } else {
                            context_data_position++;
                        }
                        value = value >> 1;
                    }
                    // Flush the last char
                    while (true) {
                        context_data_val = (context_data_val << 1);
                        if (context_data_position === bitsPerChar - 1) {
                            context_data.push(getCharFromInt(context_data_val));
                            break;
                        } else context_data_position++;
                    }
                    return context_data.join('');
                },
                decompress: function (compressed) {
                    if (compressed === null) return "";
                    if (compressed === "") return null;
                    return LZString._decompress(compressed.length, 32768, function (index) {
                        return compressed.charCodeAt(index);
                    });
                },
                _decompress: function (length, resetValue, getNextValue) {
                    let dictionary = [],
                        next,
                        enlargeIn = 4,
                        dictSize = 4,
                        numBits = 3,
                        entry = "",
                        result = [],
                        i,
                        w,
                        bits, resb, maxpower, power,
                        c,
                        data = {
                            val: getNextValue(0),
                            position: resetValue,
                            index: 1
                        };
                    for (i = 0; i < 3; i += 1) {
                        dictionary[i] = i;
                    }
                    bits = 0;
                    maxpower = Math.pow(2, 2);
                    power = 1;
                    while (power !== maxpower) {
                        resb = data.val & data.position;
                        data.position >>= 1;
                        if (data.position === 0) {
                            data.position = resetValue;
                            data.val = getNextValue(data.index++);
                        }
                        bits |= (resb > 0 ? 1 : 0) * power;
                        power <<= 1;
                    }
                    switch (next = bits) {
                        case 0:
                            bits = 0;
                            maxpower = Math.pow(2, 8);
                            power = 1;
                            while (power !== maxpower) {
                                resb = data.val & data.position;
                                data.position >>= 1;
                                if (data.position === 0) {
                                    data.position = resetValue;
                                    data.val = getNextValue(data.index++);
                                }
                                bits |= (resb > 0 ? 1 : 0) * power;
                                power <<= 1;
                            }
                            c = f(bits);
                            break;
                        case 1:
                            bits = 0;
                            maxpower = Math.pow(2, 16);
                            power = 1;
                            while (power !== maxpower) {
                                resb = data.val & data.position;
                                data.position >>= 1;
                                if (data.position === 0) {
                                    data.position = resetValue;
                                    data.val = getNextValue(data.index++);
                                }
                                bits |= (resb > 0 ? 1 : 0) * power;
                                power <<= 1;
                            }
                            c = f(bits);
                            break;
                        case 2:
                            return "";
                    }
                    dictionary[3] = c;
                    w = c;
                    result.push(c);
                    while (true) {
                        if (data.index > length) {
                            return "";
                        }
                        bits = 0;
                        maxpower = Math.pow(2, numBits);
                        power = 1;
                        while (power !== maxpower) {
                            resb = data.val & data.position;
                            data.position >>= 1;
                            if (data.position === 0) {
                                data.position = resetValue;
                                data.val = getNextValue(data.index++);
                            }
                            bits |= (resb > 0 ? 1 : 0) * power;
                            power <<= 1;
                        }
                        switch (c = bits) {
                            case 0:
                                bits = 0;
                                maxpower = Math.pow(2, 8);
                                power = 1;
                                while (power !== maxpower) {
                                    resb = data.val & data.position;
                                    data.position >>= 1;
                                    if (data.position === 0) {
                                        data.position = resetValue;
                                        data.val = getNextValue(data.index++);
                                    }
                                    bits |= (resb > 0 ? 1 : 0) * power;
                                    power <<= 1;
                                }
                                dictionary[dictSize++] = f(bits);
                                c = dictSize - 1;
                                enlargeIn--;
                                break;
                            case 1:
                                bits = 0;
                                maxpower = Math.pow(2, 16);
                                power = 1;
                                while (power !== maxpower) {
                                    resb = data.val & data.position;
                                    data.position >>= 1;
                                    if (data.position === 0) {
                                        data.position = resetValue;
                                        data.val = getNextValue(data.index++);
                                    }
                                    bits |= (resb > 0 ? 1 : 0) * power;
                                    power <<= 1;
                                }
                                dictionary[dictSize++] = f(bits);
                                c = dictSize - 1;
                                enlargeIn--;
                                break;
                            case 2:
                                return result.join('');
                        }
                        if (enlargeIn === 0) {
                            enlargeIn = Math.pow(2, numBits);
                            numBits++;
                        }
                        if (dictionary[c]) {
                            entry = dictionary[c];
                        } else {
                            if (c === dictSize) {
                                entry = w + w.charAt(0);
                            } else {
                                return null;
                            }
                        }
                        result.push(entry);
                        // Add w+entry[0] to the dictionary.
                        dictionary[dictSize++] = w + entry.charAt(0);
                        enlargeIn--;
                        w = entry;
                        if (enlargeIn === 0) {
                            enlargeIn = Math.pow(2, numBits);
                            numBits++;
                        }
                    }
                }
            };
            return LZString;
        })();
    }
    /* eslint-enable */
}

/* eslint-enable no-unused-vars */

// Export for use as a library
if (typeof module !== 'undefined' && module.exports) {
    module.exports = GoogleLinkEnhancer;
} else if (typeof window !== 'undefined') {
    window.GoogleLinkEnhancer = GoogleLinkEnhancer;
}