'use strict';
const assert = require('node:assert/strict');
const Y = require('./engine.js');
const strings = a => a.map(String);
let checks = 0;
function expansion(source, n, expected) {
    const value = Y.expand(source, n);
    assert.deepEqual(strings(value.result), expected.split(',').filter(Boolean));
    checks++;
    return value;
}

// The copied root uses the removed last column's lower parent relation.
const seam = expansion([1, 2, 4], 2, '1,2,3,4');
assert.equal(seam.after.layers[0].parents[0][2], 1);
assert.equal(seam.after.layers[0].parents[0][3], 2);
expansion([1, 3], 3, '1,2,4,8');
expansion([1, 4], 3, '1,3,9,27');
expansion([1, 3, 2], 3, '1,3,1,3,1,3,1,3');
expansion([1, 3, 4, 3], 3, '1,3,4,2,5,9,4,9,18,8,17,35');
expansion([1, 3, 4, 2, 5, 6, 5], 3, '1,3,4,2,5,6,4,9,10,8,17,18,16,33,34');

// These expose confusing pseudo-parent chains with vertex reachability.
for (const source of [[1, 2, 5, 6, 8, 5], [1, 3, 8, 9, 11, 8],
    [1, 16, 17, 20, 23, 24, 27, 20], [1, 12, 3, 14, 15, 26, 17, 14]]) {
    const value = Y.expand(source, 3);
    const fresh = Y.build(value.result);
    for (let l = 0; l < Math.min(fresh.layers.length, value.after.layers.length); l++) {
        assert.deepEqual(value.after.layers[l].parents, fresh.layers[l].parents,
            `Parent graph differs after expanding ${source}, layer ${l}`);
    }
    checks++;
}

// Zero copies must delete exactly the last term even when extraction occurs.
for (const source of [[1], [1, 1], [1, 3], [1, 4, 6, 4], [1, 3, 8, 9, 11, 8]]) {
    assert.deepEqual(strings(Y.expand(source, 0).result), strings(source.slice(0, -1)));
    checks++;
}

// Reachability is independent evidence for the standard-form checker.
const queue = [[1n, 2n], [1n, 3n], [1n, 4n]];
const seen = new Set(queue.map(s => s.join(',')));
for (let step = 0; step < queue.length && step < 2000; step++) {
    const source = queue[step];
    assert.equal(Y.checkStandard(source).status, 'standard',
        `Reachable sequence rejected: ${source}`);
    for (let n = 1; n <= 3; n++) {
        const result = Y.expand(source, n).result;
        for (let length = 1; length <= Math.min(9, result.length); length++) {
            const prefix = result.slice(0, length);
            if (prefix.some(v => v > 15n)) continue;
            const key = prefix.join(',');
            if (!seen.has(key)) { seen.add(key); queue.push(prefix); }
        }
    }
    checks++;
}
console.log(`Independent audit passed: ${checks} cases.`);
