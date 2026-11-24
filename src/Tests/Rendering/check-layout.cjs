// Run after `lake build Rendering Tests.Rendering.Gallery`, with Playwright available to Node.
// Outputs are temporary and intentionally live under ignored Scratch/.
const fs = require('node:fs');
const path = require('node:path');
const { spawnSync } = require('node:child_process');
const { pathToFileURL } = require('node:url');
const assert = require('node:assert/strict');
const mathAxisFailures = require('./math-axis.cjs');
const { chromium } = require('playwright');
const root = path.resolve(__dirname, '../../..');
const galleryName = process.env.CC_GALLERY || 'Gallery.lean';
const outputName = galleryName === 'Gallery.lean' ? 'CCWidgetVisual' : 'CCInterfaceVisual';
const output = path.join(root, 'Scratch', outputName);
fs.mkdirSync(output, {recursive:true});
const bodyFile = `Scratch/${outputName}/body.html`;
const helper = `open Lean Elab Command Term CCWidget ProofWidgets
#eval IO.FS.writeFile "${bodyFile}" ""
#eval IO.FS.writeFile "Scratch/${outputName}/inspectors.html" exportedInspectorScript
elab "capture_diagram " t:term : command => do
  let output ← runTermElabM fun _ => do
    let some j ← elabView t | throwError "unrecognized gallery term"
    match staticHtml (panel (renderJudgment j #[])) with
    | .ok output => pure output
    | .error error => throwError "{error}"
  IO.FS.withFile "${bodyFile}" .append fun h => h.putStr output
`;
const gallery = fs.readFileSync(path.join(__dirname, galleryName), 'utf8');
fs.writeFileSync(path.join(output,'Export.lean'), gallery.replace(/^open /m,helper+'\nopen ').replaceAll('#cc_diagram_show','capture_diagram'));
const lean = spawnSync('lake',['env','lean',`Scratch/${outputName}/Export.lean`],{cwd:root,encoding:'utf8'});
assert.equal(lean.status,0,lean.stdout+lean.stderr);
const doc = '<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="color-scheme" content="light dark"><title>CC diagram gallery</title><style>body{margin:0;padding:16px;box-sizing:border-box}main{max-width:1280px;margin:auto}h1{font:500 20px system-ui}</style></head><body><main><h1>CC diagram gallery</h1>'+fs.readFileSync(path.join(root,bodyFile),'utf8')+'</main></body></html>';
fs.writeFileSync(path.join(output,'gallery.html'),doc);
const inspectorScript=fs.readFileSync(path.join(output,'inspectors.html'),'utf8');
fs.writeFileSync(path.join(output,'gallery.html'),doc.replace('</body>',inspectorScript+'</body>'));
(async()=>{
 const browser=await chromium.launch({headless:true,...(process.env.CC_CHROME_EXECUTABLE?{executablePath:process.env.CC_CHROME_EXECUTABLE}:{})});
 const results=[];
 let baseline;
 try {
  for(const theme of ['light','dark','forced']) for(const width of [280,320,460,480,760,800,1024,1440]) {
   const page=await browser.newPage({viewport:{width,height:1000},colorScheme:theme==='dark'?'dark':'light',forcedColors:theme==='forced'?'active':'none'});
   const errors=[];
   page.on('pageerror',error=>errors.push(error.message));
   const requests=[];
   page.on('request',req=>{if(!req.url().startsWith('file:')) requests.push(req.url());});
   await page.goto(pathToFileURL(path.join(output,'gallery.html')).href);
   assert.equal(await page.locator('script[data-cc-inspectors]').count(),1);
   assert.equal(await page.locator('script[data-cc-inspectors]').textContent(),
    fs.readFileSync(path.join(root,'src/Rendering/inspector.js'),'utf8')+
    '\nenhanceExportedInspectors();\n','exported controller is stale or term-derived');
   if(!baseline) assert.equal(await page.locator('.ccw > style').first().textContent(),
    fs.readFileSync(path.join(root,'src/Rendering/cc-diagram.css'),'utf8'),
    'the compiled widget contains a stale stylesheet');
   const boundaryLabels=await page.locator('.cc-interface-label').evaluateAll(labels=>
    labels.map(label=>{
     const copy=label.cloneNode(true); copy.querySelector('.cc-inspector')?.remove();
     return copy.textContent.trim();
    }));
   assert(boundaryLabels.every(label=>!label.includes('Interface.queryBudget') &&
    !label.includes('Interface.portBudget') && label!=='⟨…⟩'),
    'expanded interface construction leaked onto the canvas');
   if(galleryName==='InterfaceGallery.lean') {
    assert(boundaryLabels.includes(''),'generated interface lost its inspector-only boundary');
    assert(boundaryLabels.includes('Cache 3'),'named interface label disappeared');
    assert(boundaryLabels.includes('I₃'),'explicit name for an expanded interface disappeared');
    const names=await page.locator('.cc-object-label').allTextContents();
    for(const name of ['𝟙','Counter₃','BC 7','Counter pass-through','Independent bits','Identity pair'])
     assert(names.includes(name),`missing displayed name: ${name}`);
    assert(names.every(name=>!/^𝟙\s/.test(name)),'identity node repeats its interface argument');
   }
   assert.deepEqual(await page.evaluate(mathAxisFailures),[],
     `mathematical alignment: ${theme}/${width}`);
   const report=await page.evaluate(()=>{
    const panels=[...document.querySelectorAll('.ccw')];
    const overlaps=[],clipped=[],labelOverlaps=[],wireFailures=[],frameFailures=[];
    for(const [i,panel] of panels.entries()){
     const nodes=[...panel.querySelectorAll('.cc-node')];
     for(const [a,n] of nodes.entries()){
      const b=n.getBoundingClientRect();
      for(const m of nodes.slice(a+1)){
       const c=m.getBoundingClientRect();
       if(Math.min(b.right,c.right)-Math.max(b.left,c.left)>1 && Math.min(b.bottom,c.bottom)-Math.max(b.top,c.top)>1) overlaps.push({i,left:n.textContent,right:m.textContent});
      }
      if(n.scrollWidth>n.clientWidth+2 || n.scrollHeight>n.clientHeight+2) clipped.push({i,text:n.textContent});
     }
     for(const label of panel.querySelectorAll('.cc-boundary, .cc-wire-label')) {
      const b=label.getBoundingClientRect();
      for(const node of nodes) {
       const c=node.getBoundingClientRect();
       if(Math.min(b.right,c.right)-Math.max(b.left,c.left)>1 && Math.min(b.bottom,c.bottom)-Math.max(b.top,c.top)>1) labelOverlaps.push({i,label:label.textContent,node:node.textContent});
      }
     }
     for(const wire of panel.querySelectorAll('.cc-wire')) {
      const p=wire.parentElement, prev=wire.previousElementSibling, next=wire.nextElementSibling;
      if(!prev || !next || !p.matches('.cc-attachment,.cc-serial')) {
       wireFailures.push({i,reason:'wire has no pair of components'}); continue;
      }
      const b=wire.getBoundingClientRect(), a=prev.getBoundingClientRect(), c=next.getBoundingClientRect();
      const vertical=getComputedStyle(p).flexDirection==='column';
      const near=(x,y)=>Math.abs(x-y)<=1;
      if(vertical) {
       const x=b.left+b.width/2;
       const stroke=getComputedStyle(wire,'::before');
       if(!near(b.top,a.bottom) || !near(b.bottom,c.top) ||
          !near(x,a.left+a.width/2) || !near(x,c.left+c.width/2) ||
          !near(parseFloat(stroke.top),0) || !near(parseFloat(stroke.bottom),0) ||
          stroke.borderLeftStyle!=='solid' || parseFloat(stroke.borderLeftWidth)<1)
        wireFailures.push({i,reason:'vertical connection is interrupted or detached'});
       const label=wire.querySelector('.cc-wire-label');
       if(label) {
        const text=label.firstElementChild.getBoundingClientRect();
        if(text.left<x+5 || text.top<b.top || text.bottom>b.bottom)
         wireFailures.push({i,reason:'label covers or escapes the vertical connection'});
       }
      } else if(!near(b.left,a.right) || !near(b.right,c.left) ||
                !near(b.top+b.height/2,a.top+a.height/2) ||
                !near(b.top+b.height/2,c.top+c.height/2) ||
                getComputedStyle(wire).borderBottomStyle!=='solid') {
       wireFailures.push({i,reason:'horizontal connection is interrupted or detached'});
      }
     }
     for(const group of panel.querySelectorAll('.cc-parallel,.cc-serial,.cc-named-composition')) {
      const label=group.querySelector(':scope > .cc-group-label');
      const g=group.getBoundingClientRect(), l=label.getBoundingClientRect();
      const style=getComputedStyle(group);
      if(l.top<=g.top || l.bottom>=g.bottom || l.left<=g.left || l.right>=g.right ||
         !['Top','Right','Bottom','Left'].every(side=>style[`border${side}Style`]==='solid'))
       frameFailures.push({i,reason:'operator interrupts the group boundary'});
     }
    }
    return {pageWidth:document.documentElement.scrollWidth, viewport:innerWidth,
     sources:panels.map(p=>p.querySelector('.cc-source').textContent),
     nodes:panels.map(p=>[...p.querySelectorAll('.cc-node')].map(n=>n.dataset.source)),
     localScroll:panels.map(p=>{const e=p.querySelector('.cc-comparison');return e.scrollWidth>e.clientWidth+1}),
     injected:document.querySelectorAll('img,script:not([data-cc-inspectors])').length,
     overlaps,clipped,labelOverlaps,wireFailures,frameFailures,
     math:document.querySelectorAll('math').length,
     interfaces:[...document.querySelectorAll('.cc-interface-info')].map(e=>e.textContent),
     direction:getComputedStyle(document.querySelector('.cc-attachment')).flexDirection};
   });
   assert.equal(report.pageWidth,width,`page overflow: ${theme}/${width}`);
   assert.equal(report.injected,0,'Lean text became executable markup');
   assert.deepEqual(report.overlaps,[],`overlapping boxes: ${theme}/${width}`);
   assert.deepEqual(report.clipped,[],`clipped labels: ${theme}/${width}`);
   assert.deepEqual(report.labelOverlaps,[],`interface labels overlap boxes: ${theme}/${width}`);
   assert.deepEqual(report.wireFailures,[],`broken or dangling connections: ${theme}/${width}`);
   assert.deepEqual(report.frameFailures,[],`broken group boundaries: ${theme}/${width}`);
   assert.deepEqual(errors,[],'browser error');
   assert.deepEqual(requests,[],'the static diagram made a network request');
   assert(report.math>0,'native math typography is missing');
   if(!baseline) baseline={sources:report.sources,nodes:report.nodes,interfaces:report.interfaces};
   assert.deepEqual({sources:report.sources,nodes:report.nodes,interfaces:report.interfaces},baseline,'responsive layout changed content');
   // Information opens outside the drawing: its text must fit and its trigger must not move nodes.
   let inspected=0;
   for(const inspector of await page.locator('.cc-inspector-export').all()) {
    const measure=()=>page.locator('.cc-node').evaluateAll(nodes=>nodes.map(n=>{
     const b=n.getBoundingClientRect();return [b.x+scrollX,b.y+scrollY,b.width,b.height];
    }));
    await inspector.locator('.cc-inspector-trigger').focus();
    const before=await measure();
    await page.keyboard.press('Enter');
    const popup=inspector.locator('.cc-inspector-body');
    assert(await popup.isVisible());
    assert.deepEqual(await measure(),before,'opening interface information moved a component');
    const geometry=await popup.evaluate(e=>{
     const b=e.getBoundingClientRect();return {x:b.x,y:b.y,right:b.right,bottom:b.bottom,
      width:innerWidth,height:innerHeight,client:e.clientWidth,scroll:e.scrollWidth};
    });
    assert(geometry.x>=0 && geometry.y>=0 && geometry.right<=geometry.width &&
      geometry.bottom<=geometry.height && geometry.scroll<=geometry.client+1,
      `interface inspector escapes viewport: ${JSON.stringify(geometry)}`);
    if(galleryName==='InterfaceGallery.lean' && inspected===0 && width>=480)
     assert(geometry.right-geometry.x<=320,'a short interface still occupies a wide popover');
    const cells=await popup.locator('td').evaluateAll(es=>es.map(e=>({
     width:e.clientWidth,scroll:e.scrollWidth,font:parseFloat(getComputedStyle(e).fontSize)})));
    assert(cells.every(e=>e.scroll<=e.width+1&&e.font>=12),'alphabet cells clip or shrink their text');
    const disclosure=popup.locator('.cc-interface-source > summary');
    await disclosure.click();
    await page.waitForFunction(()=>{
     const e=document.querySelector('.cc-inspector-body:popover-open');
     if(!e) return false;
     const b=e.getBoundingClientRect();
     return b.x>=0&&b.y>=0&&b.right<=innerWidth&&b.bottom<=innerHeight;
    },{},{timeout:1500});
    const expanded=await popup.boundingBox();
    assert(expanded.x>=0&&expanded.x+expanded.width<=width,'expanded source escapes the viewport');
    assert.deepEqual(await measure(),before,'expanding source moved diagram components');
    await disclosure.click();
    const collapsed=await popup.boundingBox();
    assert(Math.abs(collapsed.width-(geometry.right-geometry.x))<=1,
     'closing source did not restore the compact popover');
    inspected++;
    await popup.locator('.cc-inspector-close').click();
    assert.equal(await popup.evaluate(e=>e.matches(':popover-open')),false);
   }
   // The complete source is available on demand without crowding the diagram.
   const source=page.locator('.cc-surface > .cc-source-toggle').first();
   assert.equal(await source.getAttribute('open'),null);
   await source.locator('summary').focus();
   await page.keyboard.press('Enter');
   assert.equal(await source.locator('.cc-source').isVisible(),true);
   assert.equal(await source.locator('.cc-source').textContent(),baseline.sources[0]);
   assert.equal(await page.evaluate(()=>document.documentElement.scrollWidth),width);
   await page.keyboard.press('Enter');
   assert.equal(await source.getAttribute('open'),null);
   // Collapse/expand remains keyboard accessible and leaves content intact.
   await page.locator('.ccw > summary').first().focus();
   await page.keyboard.press('Enter');
   assert.equal(await page.locator('.ccw').first().getAttribute('open'),null);
   await page.keyboard.press('Enter');
   assert.notEqual(await page.locator('.ccw').first().getAttribute('open'),null);
   if([320,800,1440].includes(width)) await page.screenshot({path:path.join(output,`${theme}-${width}.png`),fullPage:true});
   if(galleryName==='InterfaceGallery.lean' && width===800 && theme!=='forced')
    await page.locator('.cc-named-composition').first().screenshot({
     path:path.join(output,`named-composition-${theme}.png`)});
   results.push({theme,width,cases:report.sources.length,direction:report.direction,scrollingCases:report.localScroll.flatMap((s,i)=>s?[i]:[])});
   await page.close();
  }
  fs.writeFileSync(path.join(output,'results.json'),JSON.stringify(results,null,2));
  console.log(`${baseline.sources.length} diagrams × ${results.length} viewport/theme combinations passed; continuous component connections, intact group boundaries, accessible source disclosure, stable content, no overflow, overlap, injection or network requests.`);
  console.log(path.join(output,'gallery.html'));
 } finally {await browser.close();}
})().catch(error=>{console.error(error);process.exitCode=1;});
