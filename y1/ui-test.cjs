'use strict';
const assert = require('node:assert/strict');
const path = require('node:path');
const fs = require('node:fs');
const {pathToFileURL} = require('node:url');
const {chromium} = require('C:/Users/boringsoft/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async () => {
    const browser = await chromium.launch({headless:true, executablePath:'C:/Program Files (x86)/Microsoft/Edge/Application/msedge.exe'});
    try {
        const page = await browser.newPage({viewport:{width:1400,height:1050},acceptDownloads:true});
        const errors = [], requests = [];
        page.on('pageerror', e => errors.push(e.message));
        page.on('request', req => { if(/^https?:/.test(req.url())) requests.push(req.url()); });
        await page.goto(pathToFileURL(path.join(__dirname,'..','1-Y展开器.html')).href);
        await page.waitForSelector('#mountain-after text');
        assert.equal(await page.locator('#final-result').textContent(), '1,4,6,3,10,21,9,28,68,27,82,215');
        assert(await page.locator('#mountain-before').textContent().then(t=>t.includes('R ω·2')));
        assert.equal(await page.locator('#final-result .num').first().evaluate(e=>e.style.color), 'rgb(239, 68, 68)');
        assert.equal(await page.locator('#final-result .num').nth(3).evaluate(e=>e.style.color), 'rgb(0, 191, 255)');
        assert.equal(await page.locator('#final-result .num').nth(6).evaluate(e=>e.style.color), 'rgb(238, 180, 34)');
        assert.equal(await page.locator('#mountain-before text[data-layer="0"][data-row="0"][data-column="0"]').getAttribute('fill'), '#ef4444');
        await page.screenshot({path:path.join(__dirname,'preview.png'),fullPage:true});

        // Input events, scale re-rendering and clickable result prefixes.
        await page.locator('#sequence').fill('1,3,8,9,11,8');
        assert.equal(await page.locator('#error-message').isVisible(), false);
        assert.equal(await page.locator('#final-result').textContent(), '1,3,8,9,11,7,16,17,19,15,32,33,35,31,64,65,67');
        const oldWidth = Number(await page.locator('#mountain-after').getAttribute('width'));
        await page.locator('#scale-slider').fill('50');
        assert.equal(Number(await page.locator('#mountain-after').getAttribute('width')), oldWidth / 2);
        await page.locator('#final-result .num').nth(2).click();
        assert.equal(await page.locator('#sequence').inputValue(), '1,3,8');
        await page.locator('#sequence').fill('1,2,4');
        await page.getByRole('button',{name:'标准式判断',exact:true}).click();
        assert((await page.locator('#standard-result').textContent()).includes('✓ 是标准式'));

        // JPG export really loads the SVG into a canvas and produces a JPEG.
        for (const [button, filename] of [['保存展开前(.JPG)','before.jpg'],['保存展开后(.JPG)','after.jpg'],['合并保存(.JPG)','merged.jpg']]) {
            const downloadPromise = page.waitForEvent('download');
            await page.getByRole('button',{name:button,exact:true}).click();
            const download = await downloadPromise;
            const dest = path.join(__dirname,filename);
            await download.saveAs(dest);
            const bytes = fs.readFileSync(dest);
            assert.equal(bytes[0],0xff); assert.equal(bytes[1],0xd8);
            assert(bytes.length>1000);
        }
        await page.locator('#sequence').fill('1,3abc');
        assert.equal(await page.locator('#error-message').isVisible(), true);
        assert.equal(await page.locator('#mountain-before text').count(),0);
        assert.equal(await page.locator('#mountain-after text').count(),0);
        assert(await page.getByRole('button',{name:'合并保存(.JPG)',exact:true}).isDisabled());
        await page.locator('#sequence').fill('1');
        assert.equal(await page.locator('#final-result').textContent(),'∅');
        assert.equal(await page.locator('#mountain-after').textContent(),'∅');
        await page.locator('#sequence').fill('');
        assert.equal(await page.locator('#final-result').textContent(),'∅');
        await page.locator('#sequence').fill('1,3');
        await page.locator('#repetitions').fill('0');
        assert.equal(await page.locator('#final-result').textContent(),'1');
        await page.locator('#repetitions').fill('-1');
        assert.equal(await page.locator('#error-message').isVisible(),true);
        await page.locator('#repetitions').fill('3');
        assert.equal(await page.locator('#final-result').textContent(),'1,2,4,8');
        await page.setViewportSize({width:390,height:844});
        await page.locator('#sequence').fill('1,4,6,4');
        assert(await page.evaluate(()=>document.documentElement.scrollWidth<=window.innerWidth));
        assert.deepEqual(errors,[]);
        assert.deepEqual(requests,[]);
        console.log('PASS: offline browser rendering, ordinal labels, colors, input/click/scale, standard check, 3 JPEG exports, error/empty/N=0/mobile states.');
    } finally { await browser.close(); }
})().catch(e => { console.error(e); process.exitCode=1; });
