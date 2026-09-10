/* 1-Y: finite rows carry their own immutable parent relation.
 * A pair of mountain legs is represented by parents[row][column].
 * Values are BigInt; column and finite row indices are ordinary integers.
 */
'use strict';
const Y1 = (() => {
    const LIMITS = {columns: 3000, cells: 250000, layers: 256, rows: 3000, operations: 8000000};
    class Budget {
        constructor() { this.operations = 0; this.cells = 0; }
        work(n = 1) {
            this.operations += n;
            if (this.operations > LIMITS.operations) throw new Error('计算量超过当前上限，请缩短序列或减少复制次数。');
        }
        row(n) {
            this.cells += n;
            if (this.cells > LIMITS.cells) throw new Error('山脉图过大，请缩短序列或减少复制次数。');
        }
    }
    function parseSequence(text) {
        if (!text.trim() || text.trim() === '∅') return [];
        const tokens = text.trim().split(/[,，\s]+/);
        if (tokens.length > LIMITS.columns) throw new Error(`序列最多支持 ${LIMITS.columns} 项。`);
        return tokens.map(t => {
            if (!/^\d+$/.test(t) || BigInt(t) < 1n) throw new Error('每一项必须是正整数，请用逗号或空格分隔。');
            if (t.length > 1000) throw new Error('单项数字过长（最多 1000 位）。');
            return BigInt(t);
        });
    }
    function normalParents(seq) {
        const parents = [], stack = [];
        for (let c = 0; c < seq.length; c++) {
            while (stack.length && seq[stack[stack.length - 1]] >= seq[c]) stack.pop();
            parents.push(stack.length ? stack[stack.length - 1] : -1);
            stack.push(c);
        }
        return parents;
    }
    function restrictedParents(row, previous, budget) {
        return row.map((value, c) => {
            if (value === null) return -1;
            for (let p = previous[c]; p !== -1; p = previous[p]) {
                budget.work();
                if (row[p] !== null && row[p] < value) return p;
            }
            return -1;
        });
    }
    function finishLayer(layer) {
        const n = layer.rows[0].length;
        layer.heights = Array(n).fill(0);
        for (let r = 0; r < layer.rows.length; r++) {
            for (let c = 0; c < n; c++) if (layer.rows[r][c] !== null) layer.heights[c] = r;
        }
        return layer;
    }
    function pseudoParents(layer, budget) {
        // Walk down a left leg, then up its matching right leg until a
        // principal (top-of-column) node is reached. Do not use base parents.
        return layer.heights.map((h, c) => {
            if (h === 0) return -1;
            let p = layer.parents[h - 1][c];
            while (p !== -1) {
                budget.work();
                if (layer.heights[p] === h - 1 || layer.heights[p] === h) return p;
                p = layer.parents[h - 1][p];
            }
            return -1;
        });
    }
    function buildLayer(seq, baseParents, budget) {
        const layer = {rows: [seq.slice()], parents: [baseParents.slice()], kinds: []};
        budget.row(seq.length);
        for (let r = 0; ; r++) {
            budget.work(seq.length);
            const row = layer.rows[r], parents = layer.parents[r];
            const next = row.map((v, c) => parents[c] === -1 ? null : v - row[parents[c]]);
            if (next.every(v => v === null)) break;
            if (r + 1 >= LIMITS.rows) throw new Error('有限阶差行数超过上限，请缩小输入。');
            budget.row(seq.length);
            layer.rows.push(next);
            layer.parents.push(restrictedParents(next, parents, budget));
        }
        finishLayer(layer);
        layer.pseudoParents = pseudoParents(layer, budget);
        return layer;
    }
    function build(seq, budget = new Budget()) {
        if (!seq.length) return {layers: [], root: null};
        const layers = [], x = seq.length - 1;
        let values = seq.slice(), parents = normalParents(seq), root = null;
        const successor = parents[x] === -1;
        for (let l = 0; l < LIMITS.layers; l++) {
            const layer = buildLayer(values, parents, budget);
            layers.push(layer);
            for (let r = 0; !root && !successor && r < layer.rows.length; r++) {
                const p = layer.parents[r][x];
                if (p !== -1 && layer.rows[r][x] - layer.rows[r][p] === 1n) {
                    root = {column: p, row: r, layer: l};
                    break;
                }
            }
            values = layer.heights.map((h, c) => layer.rows[h][c]);
            if (values.every(v => v === 1n)) return {layers, root};
            parents = restrictedParents(values, layer.pseudoParents, budget);
            if (parents.every(p => p === -1)) {
                if (root || successor) return {layers, root};
                throw new Error('末项在提取后仍无可用祖先，无法按这些规则确定坏根。');
            }
        }
        throw new Error('提取层数超过上限，请缩小输入。');
    }
    function completeLayers(layers, budget) {
        while (layers.length && layers.length < LIMITS.layers) {
            const last = layers[layers.length - 1];
            if (!last.rows.length) return layers;
            const tops = last.heights.map((h, c) => last.rows[h][c]);
            if (tops.every(v => v === 1n)) return layers;
            const parents = restrictedParents(tops, last.pseudoParents, budget);
            if (parents.every(p => p === -1)) return layers;
            layers.push(buildLayer(tops, parents, budget));
        }
        if (layers.length >= LIMITS.layers) throw new Error('提取层数超过上限，请缩小输入。');
        return layers;
    }
    function classify(layer, y, budget) {
        // Follow actual legs. A pseudo-parent shortcut through a lower row
        // is not a permitted contour path: no visit may go below the root top.
        const vertex = layer.heights.map(() => false);
        const floor = layer.heights[y];
        const children = layer.parents.map(row => row.map(() => []));
        layer.parents.forEach((row, r) => row.forEach((p, c) => {
            if (p !== -1) children[r][p].push(c);
        }));
        const seen = new Set(), queue = [[floor, y]];
        for (let i = 0; i < queue.length; i++) {
            const [r, c] = queue[i], key = r * vertex.length + c;
            if (seen.has(key)) continue;
            seen.add(key);
            budget.work();
            if (r === layer.heights[c]) vertex[c] = true;
            if (r > floor) queue.push([r - 1, c]);
            for (const child of children[r][c]) queue.push([r + 1, child]);
        }
        const contour = layer.parents.map(row => row.map(() => false));
        const reference = layer.parents.map(row => row.map(() => false));
        function horizontalReach(start, r, marks) {
            const reachable = new Set([start]);
            const pars = layer.parents[r];
            for (let c = start + 1; c < pars.length; c++) {
                budget.work();
                if (reachable.has(pars[c])) { marks[r][c] = true; reachable.add(c); }
            }
        }
        for (let c = y; c < vertex.length; c++) if (vertex[c]) horizontalReach(c, layer.heights[c], contour);
        horizontalReach(y, layer.heights[y], reference);
        layer.kinds = layer.parents.map((row, r) => row.map((p, c) => {
            if (p === -1) return '';
            if (reference[r][c]) return 'reference';
            if (contour[r][c]) return 'contour';
            return c > y && p < y ? 'fixed' : 'translation';
        }));
        return {vertex, contour, reference};
    }
    function graphFrom(layer, length) {
        const columns = Array.from({length}, () => ({parents: [], kinds: [], top: null}));
        for (let c = 0; c < Math.min(length, layer.heights.length); c++) {
            const h = layer.heights[c];
            columns[c] = {
                parents: Array.from({length: h}, (_, r) => layer.parents[r][c]),
                kinds: Array.from({length: h}, (_, r) => layer.kinds[r]?.[c] || ''),
                top: layer.rows[h][c]
            };
        }
        return columns;
    }
    function reconstruct(columns, budget) {
        if (!columns.length) return {rows: [], parents: [], heights: [], pseudoParents: [], kinds: []};
        const maxHeight = Math.max(...columns.map(c => c.parents.length));
        if (maxHeight >= LIMITS.rows) throw new Error('展开后的有限阶差行数超过上限，请减少复制次数。');
        const rows = [], parents = [], kinds = [];
        for (let r = 0; r <= maxHeight; r++) {
            budget.row(columns.length);
            rows.push(Array(columns.length).fill(null));
            parents.push(Array(columns.length).fill(-1));
            kinds.push(Array(columns.length).fill(''));
        }
        for (let c = 0; c < columns.length; c++) {
            const col = columns[c], h = col.parents.length;
            if (col.top === null) throw new Error(`第 ${c + 1} 列缺少提取值。`);
            rows[h][c] = col.top;
            for (let r = 0; r < h; r++) {
                const p = col.parents[r];
                if (!Number.isInteger(p) || p < 0 || p >= c) throw new Error(`第 ${c + 1} 列第 ${r} 行的父项未被填充。`);
                parents[r][c] = p;
                kinds[r][c] = col.kinds[r];
            }
        }
        for (let r = maxHeight - 1; r >= 0; r--) {
            for (let c = 0; c < columns.length; c++) {
                budget.work();
                if (r >= columns[c].parents.length) continue;
                const p = parents[r][c];
                if (rows[r][p] === null) throw new Error(`第 ${c + 1} 列第 ${r} 行的父项指向空项。`);
                rows[r][c] = rows[r + 1][c] + rows[r][p];
            }
        }
        const layer = {rows, parents, kinds, heights: columns.map(c => c.parents.length)};
        layer.pseudoParents = pseudoParents(layer, budget);
        return layer;
    }
    function terminalExpand(layer, root, x, n, budget) {
        const y = root.column, L = x - y, length = x + n * L;
        const columns = graphFrom(layer, Math.max(length, x + 1));
        // Keep the deleted last column's parents below the root row. At and
        // above that row its value/shape is the copied root column instead.
        const seam = columns[x], rootCol = columns[y];
        seam.parents = seam.parents.slice(0, root.row);
        seam.kinds = seam.kinds.slice(0, root.row);
        for (let r = root.row; r < rootCol.parents.length; r++) {
            seam.parents[r] = rootCol.parents[r] < y ? rootCol.parents[r] : rootCol.parents[r] + L;
            seam.kinds[r] = rootCol.kinds[r];
        }
        seam.top = rootCol.top;
        for (let c = x + 1; c < length; c++) {
            const block = Math.floor((c - y - 1) / L), source = c - block * L;
            const src = columns[source];
            columns[c] = {
                parents: src.parents.map(p => p < y ? p : p + block * L),
                kinds: src.parents.map((p, r) => p < y ? 'fixed' : src.kinds[r]), top: src.top
            };
        }
        return reconstruct(columns.slice(0, length), budget);
    }
    function lowerExpand(layer, upper, y, x, n, budget) {
        const L = x - y, length = x + n * L;
        const {contour, reference} = classify(layer, y, budget);
        const columns = graphFrom(layer, Math.max(length, x + 1));
        for (let block = 1; x + (block - 1) * L < length; block++) {
            const seam = x + (block - 1) * L;
            // The seam keeps its old parent relation even though its value
            // is replaced. Read its actual height anew for every copy.
            const rise = columns[seam].parents.length - layer.heights[y];
            if (rise < 0) throw new Error('轮廓提升高度为负，输入不满足当前展开规则。');
            for (let c = y + 1; c <= x; c++) {
                const dest = c + block * L;
                if (dest >= length) break;
                const target = {parents: [], kinds: [], top: null};
                for (let r = 0; r < layer.heights[c]; r++) {
                    budget.work();
                    const p = layer.parents[r][c];
                    const moving = contour[r][c];
                    const rr = moving ? r + rise : r;
                    target.parents[rr] = !moving && p < y ? p : p + block * L;
                    target.kinds[rr] = !moving && p < y ? 'fixed' : layer.kinds[r][c];
                    if (reference[r][c]) {
                        for (let offset = 0; offset < rise; offset++) {
                            budget.work();
                            target.parents[r + offset] = p + block * L;
                            target.kinds[r + offset] = 'reference';
                        }
                    }
                }
                columns[dest] = target;
            }
        }
        columns.length = length;
        for (let c = 0; c < length; c++) columns[c].top = upper.rows[0][c];
        return reconstruct(columns, budget);
    }
    function expand(seq, n) {
        seq = seq.map(v => BigInt(v));
        if (seq.some(v => v <= 0n)) throw new Error('每一项必须是正整数。');
        if (!Number.isSafeInteger(n) || n < 0) throw new Error('复制次数必须是非负整数。');
        const budget = new Budget(), before = build(seq, budget), root = before.root;
        const x = seq.length - 1;
        if (!root) {
            const result = seq.slice(0, -1);
            return {result, before, after: build(result, budget), root: null, originalLastIndex: x, badPartLength: 0};
        }
        const y = root.column, L = x - y, length = x + n * L;
        if (length > LIMITS.columns) throw new Error(`展开结果超过 ${LIMITS.columns} 项，请减少复制次数。`);
        const layers = Array(root.layer + 1);
        for (let l = 0; l < before.layers.length; l++) classify(before.layers[l], y, budget);
        layers[root.layer] = terminalExpand(before.layers[root.layer], root, x, n, budget);
        for (let l = root.layer - 1; l >= 0; l--) layers[l] = lowerExpand(before.layers[l], layers[l + 1], y, x, n, budget);
        completeLayers(layers, budget);
        return {result: layers[0].rows[0], before, after: {layers}, root, originalLastIndex: x, badPartLength: L};
    }
    function checkStandard(seq) {
        const steps = [];
        if (!seq.length || seq.length === 1 && seq[0] === 1n) return {status: 'standard', steps: ['空序列与单项 1 是标准式。']};
        if (seq[0] !== 1n) return {status: 'nonstandard', steps: ['标准式必须以 1 开头。']};
        let current = [1n, seq[1] + 1n], index = 2;
        try {
            for (let step = 0; step < 500; step++) {
                const output = expand(current, Math.max(1, index)).result.slice(0, index);
                steps.push(`[${current.join(',')}] → [${output.join(',')}]`);
                if (output.length < index || output[index - 1] < seq[index - 1]) return {status: 'nonstandard', steps};
                if (output[index - 1] === seq[index - 1]) {
                    if (index === seq.length) return {status: 'standard', steps};
                    index++;
                } else current = [...seq.slice(0, index - 1), seq[index - 1] + 1n];
            }
            return {status: 'unknown', steps, reason: '达到标准式检查步数上限，尚不能判定。'};
        } catch (e) { return {status: 'unknown', steps, reason: e.message}; }
    }
    return {parseSequence, normalParents, build, expand, checkStandard, LIMITS};
})();
if (typeof module !== 'undefined' && module.exports) module.exports = Y1;
