// Source fidelity, responsive geometry and keyboard expansion of the same Lean component tree.
const fs = require('node:fs');
const path = require('node:path');
const {spawnSync} = require('node:child_process');
const {pathToFileURL} = require('node:url');
const assert = require('node:assert/strict');
const {chromium} = require('playwright');
const root = path.resolve(__dirname, '../../..');
const output = path.join(root, 'Scratch/CCPseudocodeVisual');
fs.mkdirSync(output, {recursive:true});
const bodyFile = 'Scratch/CCPseudocodeVisual/body.html';
const helper = `open Lean Elab Command Term CCWidget ProofWidgets
#eval IO.FS.writeFile "${bodyFile}" ""
#eval IO.FS.writeFile "Scratch/CCPseudocodeVisual/inspectors.html" exportedInspectorScript
def appendView (h : Html) : CommandElabM Unit := do
  match staticHtml h with
  | .ok html => IO.FS.withFile "${bodyFile}" .append fun h => h.putStr html
  | .error error => throwError "{error}"
elab "capture_pseudocode " n:ident : command => do
  appendView (pseudocodePanel (← liftCoreM (elabPseudocode n)))
elab "capture_diagram " t:term : command => do
  let h ← runTermElabM fun _ => do
    let some j ← elabView t | throwError "unrecognized gallery term"
    return panel (renderJudgment j #[])
  appendView h
`;
const gallery = fs.readFileSync(path.join(__dirname, 'PseudocodeGallery.lean'), 'utf8');
fs.writeFileSync(path.join(output, 'Export.lean'), gallery
  .replace('open DSLExamples', helper+'\nopen DSLExamples')
  .replaceAll('#cc_pseudocode_show', 'capture_pseudocode')
  .replaceAll('#cc_diagram_show', 'capture_diagram')+
  '\n#cc_pseudocode_export DSLExamples.Arithmetic to "Scratch/CCPseudocodeVisual/arithmetic.html"\n');
const lean = spawnSync('lake', ['env','lean','Scratch/CCPseudocodeVisual/Export.lean'],
  {cwd:root, encoding:'utf8'});
assert.equal(lean.status, 0, lean.stdout+lean.stderr);
const doc = '<!doctype html><html lang="en"><head><meta charset="utf-8">'+
  '<meta name="viewport" content="width=device-width,initial-scale=1">'+
  '<meta name="color-scheme" content="light dark"><title>DSL pseudocode</title>'+
  '<style>body{margin:0;padding:16px;box-sizing:border-box}'+
  'main{max-width:1280px;margin:auto}</style></head><body><main>'+
  fs.readFileSync(path.join(root,bodyFile),'utf8')+'</main></body></html>';
fs.writeFileSync(path.join(output,'gallery.html'),doc);
const inspectorScript=fs.readFileSync(path.join(output,'inspectors.html'),'utf8');
fs.writeFileSync(path.join(output,'gallery.html'),doc.replace('</body>',inspectorScript+'</body>'));

(async()=>{
  const browser = await chromium.launch({headless:true,
    ...(process.env.CC_CHROME_EXECUTABLE?{executablePath:process.env.CC_CHROME_EXECUTABLE}:{})});
  const results = [];
  let baseline;
  try {
    const exported = await browser.newPage();
    await exported.goto(pathToFileURL(path.join(output,'arithmetic.html')).href);
    assert.equal(await exported.locator('.cc-pseudocode').getAttribute('data-declaration'),
      'DSLExamples.Arithmetic');
    assert((await exported.locator('.cc-pseudocode-source').textContent()).startsWith('system Arithmetic'));
    await exported.close();
    for (const theme of ['light','dark','forced']) {
      for (const width of [280,320,460,480,760,800,1024,1440]) {
        const page = await browser.newPage({viewport:{width,height:1000},
          colorScheme:theme==='dark'?'dark':'light',
          forcedColors:theme==='forced'?'active':'none'});
        const errors = [], requests = [];
        page.on('pageerror', e=>errors.push(e.message));
        page.on('request', r=>{if(!r.url().startsWith('file:')) requests.push(r.url());});
        await page.goto(pathToFileURL(path.join(output,'gallery.html')).href);
        assert.equal(await page.locator('script[data-cc-inspectors]').count(),1);
        assert.equal(await page.locator('script[data-cc-inspectors]').textContent(),
          fs.readFileSync(path.join(root,'src/Rendering/inspector.js'),'utf8')+
          '\nenhanceExportedInspectors();\n');
        const leaves = page.locator('.cc-pseudocode-leaf');
        assert.equal(await leaves.count(), 4, 'known DSL leaves lost their source');
        for (const leaf of await leaves.all()) {
          assert.equal(await leaf.getAttribute('open'), null);
          await leaf.locator(':scope > summary').focus();
          await page.keyboard.press('Enter');
          assert(await leaf.locator('.cc-pseudocode').isVisible());
        }
        const report = await page.evaluate(()=>{
          const cards = [...document.querySelectorAll('.cc-pseudocode')];
          const problems = [];
          const sources = cards.map(card=>{
            const heading = card.querySelector('.cc-pseudocode-heading').textContent;
            const parts = [...card.querySelector('.cc-pseudocode-sections').children];
            const source = card.querySelector('.cc-pseudocode-source').textContent;
            const reassembled = heading+parts.map(p=>p.querySelector('pre').textContent).join('');
            if (source!==reassembled) problems.push({reason:'source changed',name:card.dataset.declaration});
            const visible = parts.filter(p=>p.getBoundingClientRect().height>0);
            for (let i=0;i<visible.length;i++) for (let j=i+1;j<visible.length;j++) {
              const a=visible[i].getBoundingClientRect(),b=visible[j].getBoundingClientRect();
              if(Math.min(a.right,b.right)-Math.max(a.left,b.left)>1 &&
                 Math.min(a.bottom,b.bottom)-Math.max(a.top,b.top)>1)
                problems.push({reason:'overlapping sections',name:card.dataset.declaration});
            }
            return {name:card.dataset.declaration,source};
          });
          for(const pre of document.querySelectorAll('.cc-pseudocode pre')) {
            if(pre.getBoundingClientRect().height && pre.scrollWidth>pre.clientWidth+1)
              problems.push({reason:'clipped text',text:pre.textContent});
          }
          for(const wire of document.querySelectorAll('.cc-wire')) {
            const prev=wire.previousElementSibling, next=wire.nextElementSibling;
            const b=wire.getBoundingClientRect(),a=prev.getBoundingClientRect(),c=next.getBoundingClientRect();
            const vertical=getComputedStyle(wire.parentElement).flexDirection==='column';
            const near=(x,y)=>Math.abs(x-y)<=1;
            if(vertical ? !(near(b.top,a.bottom)&&near(b.bottom,c.top)) :
              !(near(b.left,a.right)&&near(b.right,c.left)))
              problems.push({reason:'expansion detached a connection'});
          }
          return {sources,problems,width:document.documentElement.scrollWidth,
            injected:document.querySelectorAll('img,script:not([data-cc-inspectors])').length};
        });
        assert.equal(report.width,width,`page overflow ${theme}/${width}`);
        assert.equal(report.injected,0);
        assert.deepEqual(report.problems,[],`${theme}/${width}`);
        assert.deepEqual(errors,[]);
        assert.deepEqual(requests,[]);
        baseline ??= report.sources;
        assert.deepEqual(report.sources,baseline,'responsive layout changed source');
        assert.equal(report.sources.length,19);
        assert(report.sources.some(s=>s.source.includes('<script>')),'escape case missing');
        assert(report.sources.some(s=>s.source.includes('←$')),'sampling case missing');
        const proof=page.locator('.cc-pseudocode-proof').first();
        await proof.locator('summary').focus();
        await page.keyboard.press('Enter');
        assert(await proof.locator('pre').isVisible());
        const source=page.locator('.cc-pseudocode > .cc-source-toggle').first();
        await source.locator('summary').focus();
        await page.keyboard.press('Enter');
        assert(await source.locator('pre').isVisible());
        assert.equal(await source.locator('pre').textContent(),baseline[0].source);
        assert.equal(await page.evaluate(()=>document.documentElement.scrollWidth),width);
        if([320,800,1440].includes(width))
          await page.screenshot({path:path.join(output,`${theme}-${width}.png`),fullPage:true});
        for (const leaf of await leaves.all()) {
          await leaf.locator(':scope > summary').focus();
          await page.keyboard.press('Enter');
          assert.equal(await leaf.getAttribute('open'),null);
        }
        results.push({theme,width,cards:report.sources.length});
        await page.close();
      }
    }
    fs.writeFileSync(path.join(output,'results.json'),JSON.stringify(results,null,2));
    console.log(`${results.length} viewport/theme combinations; ${baseline.length} source-backed cards: passed`);
  } finally { await browser.close(); }
})().catch(e=>{console.error(e);process.exitCode=1;});
