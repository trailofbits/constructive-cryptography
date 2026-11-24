// Actual Lean projections, rendered at narrow and wide widths with no network dependencies.
const assert = require('node:assert/strict');
const mathAxisFailures = require('./math-axis.cjs');
const fs = require('node:fs');
const path = require('node:path');
const {spawnSync} = require('node:child_process');
const {pathToFileURL} = require('node:url');
const {chromium} = require('playwright');
const root = path.resolve(__dirname, '../../..');
const out = path.join(root, 'Scratch/CCProofVisual');
fs.mkdirSync(out, {recursive:true});
const helper = `open Lean Elab Command CCWidget ProofWidgets
#eval IO.FS.writeFile "Scratch/CCProofVisual/body.html" ""
elab "capture_proof " t:term : command => do
  let html ← runTermElabM fun _ => elabProofView t false
  let .ok text := staticHtml html | throwError "proof export failed"
  IO.FS.withFile "Scratch/CCProofVisual/body.html" .append fun f => f.putStr text
`;
let source = fs.readFileSync(path.join(__dirname, 'ProofGallery.lean'), 'utf8');
source = source.replace('import Tests.Rendering.Proofs',
  'import Tests.Rendering.ProofAutomatic\n' + helper).replaceAll('#cc_proof_show', 'capture_proof');
source += `
#cc_proof_export Rendering.ProofGallery.Concrete.counterArgument
  to "Scratch/CCProofVisual/argument.html"
run_cmd do
  let rungs ← Rendering.ProofAutomaticTests.calculationRungs
    (← getEnv) (← getOptions) Rendering.ProofAutomaticTests.calculation
  let .ok text := staticHtml (panel (renderRungs rungs #[] default false))
    | throwError "calculation export failed"
  IO.FS.withFile "Scratch/CCProofVisual/body.html" .append fun f => f.putStr text
run_cmd do
  let rungs ← Rendering.ProofAutomaticTests.calculationRungs
    (← getEnv) (← getOptions) Rendering.ProofAutomaticTests.hCalculation
  let .ok text := staticHtml (.element "section" #[("id", .str "h-calculation")]
    #[panel (renderRungs rungs #[] default false)])
    | throwError "H calculation export failed"
  IO.FS.withFile "Scratch/CCProofVisual/body.html" .append fun f => f.putStr text
#eval do
  let body ← IO.FS.readFile "Scratch/CCProofVisual/body.html"
  let .ok empty := htmlDocument "Proof views" (.text "") | throw (IO.userError "export failed")
  IO.FS.writeFile "Scratch/CCProofVisual/gallery.html"
    (empty.replace "<main></main>" ("<main>" ++ body ++ "</main>"))
`;
fs.writeFileSync(path.join(out,'Export.lean'),source);
const lean = spawnSync('lake',['env','lean','Scratch/CCProofVisual/Export.lean'],
  {cwd:root,encoding:'utf8',maxBuffer:8*1024*1024});
assert.equal(lean.status,0,lean.stdout+lean.stderr);
(async()=>{
 const browser = await chromium.launch({headless:true,
  ...(process.env.CC_CHROME_EXECUTABLE ? {executablePath:process.env.CC_CHROME_EXECUTABLE} : {})});
 const reports=[];
 try {
  for(const theme of ['light','dark','forced']) for(const width of [280,320,460,760,1024,1440]) {
   const page=await browser.newPage({viewport:{width,height:1000},
    colorScheme:theme==='dark'?'dark':'light',forcedColors:theme==='forced'?'active':'none'});
   const errors=[],network=[];
   page.on('pageerror',e=>errors.push(e.message));
   page.on('request',r=>{if(!r.url().startsWith('file:')) network.push(r.url());});
   await page.goto(pathToFileURL(path.join(out,'gallery.html')).href);
   assert.equal(await page.locator('.cc-proof-view').count(),6);
   assert.equal(await page.locator('.cc-proof-justification').count() >= 5,true);
   const chains=page.locator('.cc-proof-view').filter({has:page.locator('.cc-proof-position')});
   assert.equal(await chains.count(),3);
   assert.match(await chains.nth(0).innerText(),/Premises required/);
   assert.equal(await chains.nth(0).locator('.cc-proof-position').count(),2);
   assert.equal(await chains.nth(2).locator('.cc-proof-index').count(),1);
   const hViews=page.locator('.cc-h-method');
   assert.equal(await hViews.count(),3);
   for (const argument of await hViews.all()) {
    assert.equal(await argument.locator('.cc-h-lane,.cc-h-equation').count(),0);
    assert.equal(await argument.locator('.cc-proof-method > .cc-inspector').count(),1);
    assert.equal(await argument.locator('.cc-proof-method .cc-inspector-trigger').textContent(),'H');
    assert.equal(await argument.locator('.cc-h-source > details').count() >= 22,true);
    const visible=await argument.innerText();
    assert(!/Projection|Proposition|queryBudget|HCoefficient\.|OfNat|toReal/.test(visible),visible);
    assert(visible.length<100,`argument is too verbose: ${visible.length}`);
    const r=await argument.boundingBox();
    assert(r.height<(r.width<=500?360:240),
      `argument is too tall at ${width}px: ${r.height}`);
    if(await argument.locator('.rgd').count())
     assert(r.height<240,`H comparison is too tall at ${width}px: ${r.height}`);
   }
   assert.equal(await hViews.nth(0).locator('.rgd').count(),0);
   assert.equal(await hViews.nth(1).locator('.rgd').count(),1);
   assert.equal(await hViews.nth(2).locator('.rgd').count(),0);
   const hSteps=page.locator('#h-calculation .rgd');
   assert.equal(await hSteps.count(),2);
   assert.equal(await hSteps.nth(0).locator('.cc-proof-method').count(),1);
   assert.equal(await hSteps.nth(1).locator('.cc-proof-method').count(),0);
   assert.equal(await hSteps.nth(0).locator('.cc-comparison').innerText(),
     await hViews.nth(1).locator('.cc-comparison').innerText(),
     'standalone H and calc must draw the same relation');
   const names=await chains.nth(0).locator('.cc-object-label').allTextContents();
   assert(names.includes('𝟙'),'named identity was unfolded');
   assert(names.every(s=>!s.includes('Fin.addCases')),'index implementation leaked into the diagram');
   assert.deepEqual(await page.evaluate(mathAxisFailures),[],
     `mathematical alignment: ${theme}/${width}`);
   // Exercise every ordinary disclosure, including long propositions and exact joins.
   await page.locator('details:not(.cc-inspector-static)').evaluateAll(xs=>xs.forEach(x=>{
    if(!x.closest('.cc-inspector')) x.open=true;
   }));
   const geometry=await page.evaluate(()=>{
    const bad=[];
    for(const e of document.querySelectorAll(
     '.cc-proof-field,.cc-proof-heading,.cc-proof-view,.rgd')) {
     const r=e.getBoundingClientRect();
     if(r.right>innerWidth+1 || r.left< -1 || e.scrollWidth>e.clientWidth+2)
      bad.push({class:e.className,width:r.width,scroll:e.scrollWidth,text:e.innerText.slice(0,100)});
    }
    return {page:document.documentElement.scrollWidth,width:innerWidth,bad};
   });
   assert.equal(geometry.page<=width+1,true,JSON.stringify({theme,width,geometry}));
   assert.deepEqual(geometry.bad,[],JSON.stringify({theme,width,geometry}));
   assert.deepEqual(errors,[]); assert.deepEqual(network,[]);
   // The source inspector is transient, contains every original field and stays inside the screen.
   const trigger=hViews.nth(2).locator('.cc-proof-method .cc-inspector-trigger');
   await trigger.hover();
   const popup=hViews.nth(2).locator('.cc-proof-method .cc-inspector-body');
   await popup.waitFor({state:'visible'});
   const pr=await popup.boundingBox();
   assert(pr.x>=0 && pr.x+pr.width<=width+1 && pr.y>=0 && pr.y+pr.height<=1001);
   assert.match(await popup.innerText(),/Replies/);
   await popup.locator('details').evaluateAll(xs=>xs.forEach(x=>x.open=true));
   assert(await popup.evaluate(x=>x.scrollWidth<=x.clientWidth+2),
     `expanded H-method definitions overflow at ${width}px`);
   await page.mouse.move(width-2,2);
   await popup.waitFor({state:'hidden'});
   await trigger.dblclick();
   assert.equal(await popup.getAttribute('data-pinned'),'true');
   await page.mouse.move(width-2,2);
   assert(await popup.isVisible());
   await page.mouse.click(width-2,2);
   await popup.waitFor({state:'hidden'});
   // Return to the compact default before capturing representative panels.
   await page.locator('details:not(.ccw)').evaluateAll(xs=>xs.forEach(x=>x.open=false));
   await chains.nth(0).locator('.cc-proof-static-steps > details').first().evaluate(x=>x.open=true);
   if((width===320||width===1024)&&theme!=='forced') {
    await chains.nth(0).screenshot({path:path.join(out,`chain-${theme}-${width}.png`)});
    await page.locator('.cc-proof-view').nth(5).screenshot({path:path.join(out,`h-coefficient-${theme}-${width}.png`)});
    await hSteps.nth(0).screenshot({path:path.join(out,`h-step-${theme}-${width}.png`)});
   }
   reports.push({theme,width,views:6,calculationSteps:3,hSteps:2});
   await page.close();
  }
  fs.writeFileSync(path.join(out,'checks.json'),JSON.stringify(reports,null,2));
  console.log(JSON.stringify({passed:reports.length,views:6,calculationSteps:3,hSteps:2}));
 } finally {await browser.close();}
})().catch(e=>{console.error(e);process.exitCode=1;});
