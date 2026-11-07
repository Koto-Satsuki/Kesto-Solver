document.addEventListener('DOMContentLoaded', () => {
    'use strict';

    const SIZE = 8;
    const AUTOPLAY_MS = 450;
    const BG_VALUES = ['.', '#', 'T'];
    const FG_VALUES = ['.', 'Y'];
    const TONES = {
        primary: 'var(--text-primary)',
        muted: 'var(--text-secondary)',
        ok: '#00ff88',
        warn: '#ffb02e',
        error: '#ff2a6d'
    };

    const byId = (id) => document.getElementById(id);
    const gridEl = byId('grid');
    const toolBtns = document.querySelectorAll('.tool-btn');
    const btnClear = byId('btn-clear');
    const btnSolve = byId('btn-solve');
    const btnEdit = byId('btn-edit');
    const solverMessage = byId('solver-message');
    const solutionControls = byId('solution-controls');
    const stepCurrentEl = byId('current-step');
    const stepTotalEl = byId('total-steps');
    const pathDisplay = byId('path-display');
    const btnPrev = byId('btn-prev');
    const btnPlay = byId('btn-play');
    const timeLimitInput = byId('time-limit');
    const timeLimitValue = byId('time-limit-value');
    const stateBudgetInput = byId('state-budget');
    const stateBudgetValue = byId('state-budget-value');
    const btnResetSettings = byId('btn-reset-settings');

    // ---- Controls added from script (index.html stays unchanged) ----
    const actionsEl = btnSolve.parentElement;
    const playbackEl = btnPrev.parentElement;

    const btnCancel = document.createElement('button');
    btnCancel.id = 'btn-cancel';
    btnCancel.type = 'button';
    btnCancel.className = 'action-btn secondary hidden';
    btnCancel.textContent = 'Cancel';
    btnSolve.after(btnCancel);

    const btnRestore = document.createElement('button');
    btnRestore.id = 'btn-restore';
    btnRestore.type = 'button';
    btnRestore.className = 'action-btn secondary hidden';
    btnRestore.textContent = 'Restore start board';
    btnEdit.after(btnRestore);

    const btnAuto = document.createElement('button');
    btnAuto.id = 'btn-auto';
    btnAuto.type = 'button';
    btnAuto.className = 'play-btn';
    btnAuto.title = 'Auto-play / pause';
    btnAuto.setAttribute('aria-label', 'Auto-play / pause');
    btnAuto.textContent = '▶▶';
    playbackEl.appendChild(btnAuto);

    const countsEl = document.createElement('p');
    countsEl.id = 'board-counts';
    solverMessage.after(countsEl);

    // ---- State ----
    const makeGrid = () => Array.from({ length: SIZE }, () => Array(SIZE).fill('.'));
    const cloneGrid = (g) => g.map((row) => row.slice());

    let bgGrid = makeGrid();
    let fgGrid = makeGrid();
    let cells = [];
    let currentTool = '.';

    let blockEntities = [];
    let playbackStates = [];
    let playbackPath = [];
    let playbackIdentities = [];
    let currentStep = 0;
    let startSnapshot = null;

    let isSolving = false;
    let solveToken = 0;
    let cancelActiveSolve = null;
    let solveTimer = null;
    let workerUnavailable = false;
    let autoTimer = null;

    let isDrawing = false;
    let lastDrawnKey = null;

    const defaultSearchSettings = { timeSeconds: 60, stateMillions: 30 };

    // ---- Helpers ----
    function setMessage(text, tone = 'muted') {
        solverMessage.textContent = text;
        solverMessage.style.color = TONES[tone] || TONES.muted;
    }

    function isValidGrid(g, allowed) {
        return Array.isArray(g) && g.length === SIZE && g.every((row) =>
            Array.isArray(row) && row.length === SIZE && row.every((v) => allowed.includes(v)));
    }

    function saveGrid() {
        try {
            localStorage.setItem('kestoBgGrid', JSON.stringify(bgGrid));
            localStorage.setItem('kestoFgGrid', JSON.stringify(fgGrid));
        } catch (e) {
            console.warn('Could not save grid to localStorage', e);
        }
    }

    function loadGrid() {
        try {
            const savedBg = JSON.parse(localStorage.getItem('kestoBgGrid'));
            const savedFg = JSON.parse(localStorage.getItem('kestoFgGrid'));
            if (isValidGrid(savedBg, BG_VALUES) && isValidGrid(savedFg, FG_VALUES)) {
                bgGrid = savedBg;
                fgGrid = savedFg;
                for (let r = 0; r < SIZE; r++) {
                    for (let c = 0; c < SIZE; c++) {
                        if (bgGrid[r][c] === '#') fgGrid[r][c] = '.';
                    }
                }
            }
        } catch (e) {
            console.warn('Could not load grid from localStorage', e);
        }
    }

    function updateCounts() {
        let blocks = 0;
        let targets = 0;
        for (let r = 0; r < SIZE; r++) {
            for (let c = 0; c < SIZE; c++) {
                if (fgGrid[r][c] === 'Y') blocks++;
                if (bgGrid[r][c] === 'T') targets++;
            }
        }
        const mismatch = blocks !== targets;
        countsEl.textContent = `Blocks ${blocks} · Targets ${targets}` + (mismatch ? ' (counts must match)' : '');
        countsEl.style.color = mismatch && (blocks > 0 || targets > 0) ? TONES.warn : TONES.muted;
    }

    // ---- Search settings ----
    const formatSeconds = (value) => {
        const seconds = Number(value);
        return seconds.toFixed(seconds % 1 === 0 ? 0 : 1) + 's';
    };
    const formatMillions = (value) => Number(value).toFixed(1) + 'M';

    function loadSearchSettings() {
        try {
            const saved = localStorage.getItem('kestoSearchSettings');
            if (!saved) return { ...defaultSearchSettings };
            const parsed = JSON.parse(saved);
            return {
                timeSeconds: Number.isFinite(parsed.timeSeconds) ? parsed.timeSeconds : defaultSearchSettings.timeSeconds,
                stateMillions: Number.isFinite(parsed.stateMillions) ? parsed.stateMillions : defaultSearchSettings.stateMillions
            };
        } catch (e) {
            console.warn('Could not load search settings', e);
            return { ...defaultSearchSettings };
        }
    }

    function updateSearchSettingLabels(save = true) {
        const timeSeconds = Number(timeLimitInput.value);
        const stateMillions = Number(stateBudgetInput.value);
        timeLimitValue.textContent = formatSeconds(timeSeconds);
        stateBudgetValue.textContent = formatMillions(stateMillions);
        if (save) {
            try {
                localStorage.setItem('kestoSearchSettings', JSON.stringify({ timeSeconds, stateMillions }));
            } catch (e) {
                console.warn('Could not save search settings', e);
            }
        }
    }

    function getSearchSettings() {
        return {
            maxMillis: Math.round(Number(timeLimitInput.value) * 1000),
            maxNodes: Math.round(Number(stateBudgetInput.value) * 1000000)
        };
    }

    function initSearchSettings() {
        const settings = loadSearchSettings();
        timeLimitInput.value = settings.timeSeconds;
        stateBudgetInput.value = settings.stateMillions;
        updateSearchSettingLabels(false);

        timeLimitInput.addEventListener('input', () => updateSearchSettingLabels());
        stateBudgetInput.addEventListener('input', () => updateSearchSettingLabels());
        btnResetSettings.addEventListener('click', () => {
            timeLimitInput.value = defaultSearchSettings.timeSeconds;
            stateBudgetInput.value = defaultSearchSettings.stateMillions;
            updateSearchSettingLabels();
        });
    }

    // ---- Grid rendering ----
    function updateCellClass(cell, r, c) {
        cell.className = 'cell';
        if (bgGrid[r][c] === '#') cell.classList.add('wall');
        if (bgGrid[r][c] === 'T') cell.classList.add('target');
        if (fgGrid[r][c] === 'Y') cell.classList.add('block');
    }

    function restoreGridVisuals() {
        for (let r = 0; r < SIZE; r++) {
            for (let c = 0; c < SIZE; c++) {
                updateCellClass(cells[r][c], r, c);
            }
        }
    }

    function clearBlockEntities() {
        blockEntities.forEach((el) => el.remove());
        blockEntities = [];
    }

    function initGrid() {
        gridEl.innerHTML = '';
        cells = [];
        loadGrid();
        for (let r = 0; r < SIZE; r++) {
            cells[r] = [];
            for (let c = 0; c < SIZE; c++) {
                const cell = document.createElement('div');
                cell.dataset.r = r;
                cell.dataset.c = c;
                updateCellClass(cell, r, c);
                gridEl.appendChild(cell);
                cells[r][c] = cell;
            }
        }
        blockEntities = [];
        updateCounts();
    }

    // ---- Editing (pointer events: mouse, touch and pen) ----
    function canEdit() {
        return !isSolving && solutionControls.classList.contains('hidden');
    }

    function applyTool(r, c) {
        stopAutoplay();
        solutionControls.classList.add('hidden');
        btnRestore.classList.add('hidden');
        setMessage('Board modified.');
        if (blockEntities.length > 0) {
            clearBlockEntities();
            restoreGridVisuals();
        }
        if (currentTool === '.') {
            bgGrid[r][c] = '.';
            fgGrid[r][c] = '.';
        } else if (currentTool === '#' || currentTool === 'T') {
            bgGrid[r][c] = currentTool;
            if (currentTool === '#') fgGrid[r][c] = '.';
        } else if (currentTool === 'Y') {
            fgGrid[r][c] = 'Y';
            if (bgGrid[r][c] === '#') bgGrid[r][c] = '.';
        }
        updateCellClass(cells[r][c], r, c);
        updateCounts();
        saveGrid();
    }

    function cellFromPoint(x, y) {
        const el = document.elementFromPoint(x, y);
        const cell = el && el.closest ? el.closest('.cell') : null;
        return cell && gridEl.contains(cell) ? cell : null;
    }

    function drawAt(cell) {
        const r = Number(cell.dataset.r);
        const c = Number(cell.dataset.c);
        const key = r * SIZE + c;
        if (key === lastDrawnKey) return;
        lastDrawnKey = key;
        applyTool(r, c);
    }

    function stopDrawing() {
        isDrawing = false;
        lastDrawnKey = null;
    }

    gridEl.style.touchAction = 'none';
    gridEl.addEventListener('contextmenu', (e) => e.preventDefault());
    gridEl.addEventListener('pointerdown', (e) => {
        if (e.pointerType === 'mouse' && e.button !== 0) return;
        if (!canEdit()) return;
        const cell = cellFromPoint(e.clientX, e.clientY);
        if (!cell) return;
        e.preventDefault();
        isDrawing = true;
        lastDrawnKey = null;
        drawAt(cell);
    });
    gridEl.addEventListener('pointermove', (e) => {
        if (!isDrawing) return;
        if (!canEdit()) { stopDrawing(); return; }
        const cell = cellFromPoint(e.clientX, e.clientY);
        if (cell) drawAt(cell);
    });
    window.addEventListener('pointerup', stopDrawing);
    window.addEventListener('pointercancel', stopDrawing);

    toolBtns.forEach((btn) => {
        btn.addEventListener('click', () => {
            toolBtns.forEach((b) => b.classList.remove('active'));
            btn.classList.add('active');
            currentTool = btn.dataset.tool;
        });
    });

    btnEdit.addEventListener('click', () => {
        stopAutoplay();
        solutionControls.classList.add('hidden');
        btnEdit.classList.add('hidden');
        btnSolve.classList.remove('hidden');

        const currentBlocks = playbackIdentities[currentStep] || [];
        for (let r = 0; r < SIZE; r++) {
            for (let c = 0; c < SIZE; c++) {
                fgGrid[r][c] = '.';
            }
        }
        currentBlocks.forEach((pos) => {
            if (pos) fgGrid[pos.r][pos.c] = 'Y';
        });
        clearBlockEntities();
        restoreGridVisuals();
        updateCounts();
        saveGrid();

        const changed = startSnapshot && JSON.stringify(startSnapshot) !== JSON.stringify(fgGrid);
        btnRestore.classList.toggle('hidden', !changed);
        setMessage('Edit mode.');
    });

    btnRestore.addEventListener('click', () => {
        if (!startSnapshot) return;
        fgGrid = cloneGrid(startSnapshot);
        restoreGridVisuals();
        updateCounts();
        saveGrid();
        btnRestore.classList.add('hidden');
        setMessage('Start board restored.');
    });

    btnClear.addEventListener('click', () => {
        if (isSolving) return;
        stopAutoplay();
        solutionControls.classList.add('hidden');
        btnEdit.classList.add('hidden');
        btnRestore.classList.add('hidden');
        btnSolve.classList.remove('hidden');
        startSnapshot = null;
        clearBlockEntities();
        setMessage('Board cleared.');
        for (let r = 0; r < SIZE; r++) {
            for (let c = 0; c < SIZE; c++) {
                bgGrid[r][c] = '.';
                fgGrid[r][c] = '.';
                updateCellClass(cells[r][c], r, c);
            }
        }
        updateCounts();
        saveGrid();
    });

    // ---- Solving (Web Worker with main-thread fallback) ----
    function solveOnMainThread(payload) {
        if (typeof Solver === 'undefined') throw new Error('solver.js did not load.');
        const solver = new Solver(payload.bgGrid, payload.fgGrid);
        return solver.solve(payload.maxNodes, payload.maxMillis);
    }

    function runSolver(payload) {
        return new Promise((resolve, reject) => {
            const fallback = () => {
                cancelActiveSolve = null;
                setTimeout(() => {
                    try { resolve(solveOnMainThread(payload)); } catch (err) { reject(err); }
                }, 50);
            };

            if (typeof Worker === 'undefined' || workerUnavailable) {
                fallback();
                return;
            }

            let worker = null;
            let workerUrl = null;
            const cleanup = () => {
                if (worker) worker.terminate();
                if (workerUrl) URL.revokeObjectURL(workerUrl);
                worker = null;
                workerUrl = null;
            };

            try {
                // Same URL (including any ?v= cache-buster) as the <script> tag, so the worker
                // never runs a different solver.js than the page.
                const solverTag = typeof document.querySelector === 'function'
                    ? document.querySelector('script[src*="solver.js"]')
                    : null;
                const solverUrl = solverTag && solverTag.src
                    ? solverTag.src
                    : new URL('solver.js', document.baseURI).href;
                const source = `importScripts(${JSON.stringify(solverUrl)});
self.onmessage = (e) => {
    const d = e.data;
    try {
        const solver = new Solver(d.bgGrid, d.fgGrid);
        self.postMessage({ ok: true, result: solver.solve(d.maxNodes, d.maxMillis) });
    } catch (err) {
        self.postMessage({ ok: false, error: String((err && err.message) || err) });
    }
};`;
                workerUrl = URL.createObjectURL(new Blob([source], { type: 'text/javascript' }));
                worker = new Worker(workerUrl);
            } catch (err) {
                console.warn('Web Worker unavailable, solving on the main thread.', err);
                workerUnavailable = true;
                cleanup();
                fallback();
                return;
            }

            cancelActiveSolve = cleanup;
            worker.onmessage = (e) => {
                const data = e.data;
                cleanup();
                cancelActiveSolve = null;
                if (data && data.ok) resolve(data.result);
                else reject(new Error((data && data.error) || 'Solver failed.'));
            };
            worker.onerror = (e) => {
                if (e && e.preventDefault) e.preventDefault();
                console.warn('Web Worker failed, solving on the main thread.', e && e.message);
                workerUnavailable = true;
                cleanup();
                fallback();
            };
            worker.postMessage(payload);
        });
    }

    function setSolvingUI(on) {
        isSolving = on;
        btnSolve.classList.toggle('hidden', on);
        btnCancel.classList.toggle('hidden', !on);
        btnClear.disabled = on;
        if (!on && solveTimer) {
            clearInterval(solveTimer);
            solveTimer = null;
        }
    }

    function startSolve() {
        if (isSolving) return;
        stopAutoplay();
        solutionControls.classList.add('hidden');
        btnRestore.classList.add('hidden');

        const token = ++solveToken;
        const startedAt = performance.now();
        const payload = { bgGrid: cloneGrid(bgGrid), fgGrid: cloneGrid(fgGrid), ...getSearchSettings() };

        setSolvingUI(true);
        setMessage('Solving… 0.0s', 'primary');
        solveTimer = setInterval(() => {
            if (isSolving && token === solveToken) {
                setMessage(`Solving… ${((performance.now() - startedAt) / 1000).toFixed(1)}s`, 'primary');
            }
        }, 200);

        runSolver(payload).then((result) => {
            if (token !== solveToken) return;
            setSolvingUI(false);
            showResult(result, payload);
        }).catch((err) => {
            if (token !== solveToken) return;
            console.error(err);
            setSolvingUI(false);
            setMessage('An error occurred during solving.', 'error');
        });
    }

    btnSolve.addEventListener('click', startSolve);

    btnCancel.addEventListener('click', () => {
        if (!isSolving) return;
        solveToken++;
        if (cancelActiveSolve) {
            cancelActiveSolve();
            cancelActiveSolve = null;
        }
        setSolvingUI(false);
        setMessage('Solve cancelled.');
    });

    function showResult(result, payload) {
        if (result.success) {
            const nonOptimal = /not proven/i.test(result.message || '');
            setMessage(result.message, nonOptimal ? 'warn' : 'ok');

            playbackStates = result.states;
            playbackPath = result.path;

            if (result.path.length > 0) {
                startSnapshot = cloneGrid(payload.fgGrid);
                renderPath();
                solutionControls.classList.remove('hidden');
                btnSolve.classList.add('hidden');
                btnEdit.classList.remove('hidden');
                stepTotalEl.textContent = result.path.length;
                currentStep = 0;
                computeBlockIdentities();
                renderStep(0);
            } else {
                solutionControls.classList.add('hidden');
            }
        } else {
            setMessage(result.message || 'No solution found.', 'error');
            solutionControls.classList.add('hidden');
            btnEdit.classList.add('hidden');
            btnSolve.classList.remove('hidden');
            clearBlockEntities();
            restoreGridVisuals();
        }
    }

    // ---- Playback ----
    function getBlocksFromState(state) {
        const blocks = [];
        for (let i = 0; i < SIZE * SIZE; i++) {
            if ((state >> BigInt(i)) & 1n) blocks.push({ r: i >> 3, c: i & 7 });
        }
        return blocks;
    }

    function computeBlockIdentities() {
        playbackIdentities = [];
        if (playbackStates.length === 0) return;

        const initialBlocks = getBlocksFromState(playbackStates[0]);
        initialBlocks.sort((a, b) => (a.r !== b.r ? a.r - b.r : a.c - b.c));
        playbackIdentities.push(initialBlocks);

        for (let i = 1; i < playbackStates.length; i++) {
            const dir = playbackPath[i - 1];
            const prevBlocks = playbackIdentities[i - 1].map((pos, id) => ({ r: pos.r, c: pos.c, id }));

            // Blocks never pass each other along the movement axis, so matching
            // them by sorted order keeps every block's identity.
            const sortFn = (dir === 'U' || dir === 'D')
                ? (a, b) => (a.c !== b.c ? a.c - b.c : a.r - b.r)
                : (a, b) => (a.r !== b.r ? a.r - b.r : a.c - b.c);

            prevBlocks.sort(sortFn);
            const currBlocks = getBlocksFromState(playbackStates[i]);
            currBlocks.sort(sortFn);

            const nextIdentities = new Array(initialBlocks.length);
            for (let j = 0; j < prevBlocks.length; j++) {
                nextIdentities[prevBlocks[j].id] = currBlocks[j];
            }
            playbackIdentities.push(nextIdentities);
        }
    }

    function renderPath() {
        pathDisplay.textContent = '';
        playbackPath.forEach((dir, i) => {
            const span = document.createElement('span');
            span.textContent = dir;
            pathDisplay.appendChild(span);
            if (i < playbackPath.length - 1) pathDisplay.appendChild(document.createTextNode(' → '));
        });
    }

    function highlightPath() {
        const spans = pathDisplay.querySelectorAll('span');
        let active = null;
        spans.forEach((span, i) => {
            const isActive = i === currentStep - 1;
            span.style.color = isActive ? 'var(--color-gold)' : '';
            span.style.fontWeight = '';
            if (isActive) active = span;
        });
        if (active) {
            const a = active.getBoundingClientRect();
            const p = pathDisplay.getBoundingClientRect();
            if (a.top < p.top || a.bottom > p.bottom) {
                pathDisplay.scrollTop += (a.top - p.top) - p.height / 2;
            }
        }
    }

    function renderStep(stepIndex) {
        currentStep = stepIndex;
        stepCurrentEl.textContent = stepIndex;

        for (let r = 0; r < SIZE; r++) {
            for (let c = 0; c < SIZE; c++) {
                if (fgGrid[r][c] === 'Y') cells[r][c].classList.remove('block');
            }
        }

        const blocks = playbackIdentities[stepIndex] || [];
        while (blockEntities.length < blocks.length) {
            const el = document.createElement('div');
            el.className = 'block-entity';
            gridEl.appendChild(el);
            blockEntities.push(el);
        }
        while (blockEntities.length > blocks.length) {
            blockEntities.pop().remove();
        }

        const gridRect = gridEl.getBoundingClientRect();
        blocks.forEach((pos, i) => {
            const el = blockEntities[i];
            const cellRect = cells[pos.r][pos.c].getBoundingClientRect();
            el.style.left = (cellRect.left - gridRect.left - 1) + 'px';
            el.style.top = (cellRect.top - gridRect.top - 1) + 'px';
            el.style.width = cellRect.width + 'px';
            el.style.height = cellRect.height + 'px';
            el.classList.toggle('on-target', bgGrid[pos.r][pos.c] === 'T');
        });

        highlightPath();
    }

    function nextStep() {
        renderStep(currentStep < playbackStates.length - 1 ? currentStep + 1 : 0);
    }

    function prevStep() {
        if (currentStep > 0) renderStep(currentStep - 1);
    }

    function stopAutoplay() {
        if (autoTimer) {
            clearInterval(autoTimer);
            autoTimer = null;
        }
        btnAuto.textContent = '▶▶';
    }

    function startAutoplay() {
        if (playbackStates.length < 2) return;
        if (currentStep >= playbackStates.length - 1) renderStep(0);
        btnAuto.textContent = '❚❚';
        autoTimer = setInterval(() => {
            if (currentStep < playbackStates.length - 1) renderStep(currentStep + 1);
            if (currentStep >= playbackStates.length - 1) stopAutoplay();
        }, AUTOPLAY_MS);
    }

    btnPrev.addEventListener('click', () => { stopAutoplay(); prevStep(); });
    btnPlay.addEventListener('click', () => { stopAutoplay(); nextStep(); });
    btnAuto.addEventListener('click', () => { if (autoTimer) stopAutoplay(); else startAutoplay(); });

    document.addEventListener('keydown', (e) => {
        if (solutionControls.classList.contains('hidden')) return;
        if (e.target && /^(INPUT|TEXTAREA|SELECT)$/.test(e.target.tagName)) return;
        if (e.key === 'ArrowRight') {
            stopAutoplay();
            nextStep();
        } else if (e.key === 'ArrowLeft') {
            stopAutoplay();
            prevStep();
        } else if (e.key === 'Home') {
            stopAutoplay();
            renderStep(0);
        } else if (e.key === 'End') {
            stopAutoplay();
            renderStep(playbackStates.length - 1);
        } else {
            return;
        }
        e.preventDefault();
    });

    window.addEventListener('resize', () => {
        if (!solutionControls.classList.contains('hidden')) renderStep(currentStep);
    });

    initSearchSettings();
    initGrid();
});
