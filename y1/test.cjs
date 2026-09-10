'use strict';
const assert = require('node:assert/strict');
const Y = require('./engine.js');
const parse = Y.parseSequence;
const str = xs => xs.map(x => x === null ? null : String(x));
let checks = 0;
function equal(a,b) { assert.deepEqual(a,b); checks++; }
function expand(s,n=3) { return Y.expand(parse(s),n); }

equal(str(expand('1,2').result), ['1','1','1','1']);
equal(str(expand('1,3').result), ['1','2','4','8']);
equal(str(expand('1,3,2').result), ['1','3','1','3','1','3','1','3']);
equal(str(expand('1,3,1').result), ['1','3']);
equal(str(expand('1').result), []);
equal(str(expand('').result), []);
equal(str(expand('1,3,4,3',0).result), ['1','3','4']);

const inherited = Y.build(parse('1,2,4,5,8'));
equal(inherited.layers[0].rows.map(str), [
    ['1','2','4','5','8'], [null,'1','2','1','3'], [null,null,'1',null,'2']
]);
equal(inherited.layers[0].parents[2][4], -1);
equal(inherited.root, {column:3,row:0,layer:1});
const extracted = Y.build(parse('1,3,6,8'));
equal(str(extracted.layers[1].rows[0]), ['1','2','1','2']);
equal(extracted.layers[1].parents[0][3], 0);
const wiki = Y.build(parse('1,3,7,14,7,13'));
equal(str(wiki.layers[1].rows[0]), ['1','2','2','1','2','2']);
equal(wiki.layers[1].parents[0].slice(4), [0,0]);
equal(Y.build(parse('1,3,2')).layers.length, 2);
equal(Y.build(parse('1,4,11,21')).layers.length, 3);

assert.throws(()=>parse('1,3abc'), /正整数/); checks++;
assert.throws(()=>parse('1,-2'), /正整数/); checks++;
assert.throws(()=>parse('1,0'), /正整数/); checks++;
assert.throws(()=>expand('1,3',NaN), /复制次数/); checks++;
equal(str(parse('1， 9007199254740993')), ['1','9007199254740993']);

// Structural tests check the geometric definition, not just result lengths.
function invariant(data, source, n) {
    equal(str(data.result.slice(0, source.length - 1)), str(source.slice(0,-1)));
    if (data.root) equal(data.result.length, source.length - 1 + n * data.badPartLength);
    for (let l=0;l<data.after.layers.length;l++) {
        const layer = data.after.layers[l];
        for (let r=0;r<layer.rows.length;r++) for (let c=0;c<layer.rows[r].length;c++) {
            const p = layer.parents[r][c];
            if (p === -1) continue;
            assert(p<c && p>=0);
            assert(layer.rows[r][p] !== null);
            equal(layer.rows[r][c], layer.rows[r][p]+layer.rows[r+1][c]);
        }
        if (l+1<data.after.layers.length) {
            equal(str(layer.heights.map((h,c)=>layer.rows[h][c])), str(data.after.layers[l+1].rows[0]));
        }
    }
}
const cases = [
    '1,2','1,3','1,4','1,3,2','1,4,6,4','1,3,4,3',
    '1,2,4,5,8','1,3,4,2,5,6,5','1,4,9,4','1,3,7,14,7,13',
    '1,2,4,8,10,8','1,4,11,21','1,3,6,8','1,1,4,5,1,4',
    '1,2,5,6,8,5','1,3,8,9,11,8','1,16,17,20,23,24,27,20','1,12,3,14,15,26,17,14'
];
for (const s of cases) for (const n of [0,1,2,3,5]) invariant(expand(s,n),parse(s),n);
// Exhaustively cover short positive sequences, including nonstandard ones.
let sequences=0;
function enumerate(prefix, remaining) {
    if (!remaining) {
        const s = prefix.join(',');
        try { invariant(expand(s,2),parse(s),2); }
        catch(e) { e.message = `${s}: ${e.message}`; throw e; }
        sequences++; return;
    }
    for(let x=1;x<=5;x++) enumerate([...prefix,x],remaining-1);
}
for (let n=1;n<=5;n++) enumerate([1],n-1);
equal(Y.checkStandard(parse('1,3,4')).status,'standard');
equal(Y.checkStandard(parse('1,2,4')).status,'standard');
equal(Y.checkStandard(parse('1,2,5')).status,'nonstandard');
equal(Y.checkStandard(parse('2,3')).status,'nonstandard');
console.log(`PASS: ${checks} checks, ${sequences} exhaustive sequences plus ${cases.length} targeted cases.`);
