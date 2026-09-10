const fs = require('node:fs');
const path = require('node:path');
const target = path.join(__dirname, '..', '1-Y展开器.html');
const engine = fs.readFileSync(path.join(__dirname, 'engine.js'), 'utf8');
const html = fs.readFileSync(target, 'utf8');
const pattern = /\/\/ Y1_ENGINE_PLACEHOLDER|\/\* Y1_ENGINE_START \*\/[\s\S]*?\/\* Y1_ENGINE_END \*\//;
if (!pattern.test(html)) throw new Error('Missing engine marker');
fs.writeFileSync(target, html.replace(pattern, () => `/* Y1_ENGINE_START */\n${engine}\n/* Y1_ENGINE_END */`));
console.log('Bundled standalone 1-Y展开器.html');
