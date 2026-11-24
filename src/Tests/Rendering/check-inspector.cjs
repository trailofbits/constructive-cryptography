// Exercise the actual widget JavaScript with the React runtime bundled with Lean's infoview.
const fs = require('node:fs');
const path = require('node:path');
const http = require('node:http');
const assert = require('node:assert/strict');
const {spawnSync} = require('node:child_process');
const {chromium} = require('playwright');
const root = path.resolve(__dirname,'../../..');
const output = path.join(root,'Scratch/CCInterfaceVisual');
const runtime = process.env.CC_INFOVIEW_DIR;
assert(runtime,'Set CC_INFOVIEW_DIR to the Lean extension’s dist/lean4-infoview directory.');
fs.mkdirSync(output,{recursive:true});
fs.writeFileSync(path.join(output,'Inspector.lean'),`import Rendering.Export
#eval IO.FS.writeFile "Scratch/CCInterfaceVisual/inspector.js" CCWidget.Inspector.javascript
#eval IO.FS.writeFile "Scratch/CCInterfaceVisual/inspector.css" CCWidget.stylesheet
#eval IO.FS.writeFile "Scratch/CCInterfaceVisual/inspector-export.html" CCWidget.exportedInspectorScript
`);
const lean=spawnSync('lake',['env','lean','Scratch/CCInterfaceVisual/Inspector.lean'],
  {cwd:root,encoding:'utf8'});
assert.equal(lean.status,0,lean.stdout+lean.stderr);
const html=`<!doctype html><html><head><meta name="viewport" content="width=device-width,initial-scale=1">
<link rel="stylesheet" href="/inspector.css">
<script type="importmap">{"imports":{"react":"/react.js","react-dom":"/react-dom.js"}}</script>
</head><body><button id="outside">Outside</button><div class="ccw" id="root"></div><div id="empty" style="position:fixed;inset:0 auto auto 0;width:6px;height:100vh"></div>
<script type="module">
import React from 'react'; import {createRoot} from 'react-dom'; import Inspector from '/inspector.js';
const e=React.createElement;
const content=e('div',{className:'cc-interface-info'},
 e('p',null,'Interface information'),
 e('details',{className:'cc-interface-source'},e('summary',null,'Lean'),
  e('code',null,('long source '.repeat(12)+'\\n').repeat(100))));
function Demo() {
 const [identity,update]=React.useState(0); window.changeIdentity=()=>update(n=>n+1);
 return e('div',null,e(Inspector,{label:'Outside interface',identity},content),
 e(Inspector,{label:'Inside interface'},content));
}
createRoot(document.getElementById('root')).render(e(Demo));
</script></body></html>`;
const exported=html.slice(0,html.indexOf('<script type="module">')).replace(
 '<div class="ccw" id="root"></div>', '<div class="ccw">'+
 ['Outside interface','Inside interface'].map(label=>`<details class="cc-inspector cc-inspector-static">
 <summary aria-label="${label}">ⓘ</summary><div class="cc-inspector-body">
 <div class="cc-interface-info"><p>Interface information</p>
 <details class="cc-interface-source"><summary>Lean</summary><code>${'long source '.repeat(200)}</code></details>
 </div></div></details>`).join('')+'</div>')+
 fs.readFileSync(path.join(output,'inspector-export.html'),'utf8')+'</body></html>';
const routes={
 // Concurrent infoview imports can instantiate the same widget module more than once.
 '/duplicate':['text/html',html.replace("import Inspector from '/inspector.js';",
  "import Inspector from '/inspector.js'; import InsideInspector from '/inspector-copy.js';")
  .replace("e(Inspector,{label:'Inside interface'}", "e(InsideInspector,{label:'Inside interface'}")],
 '/frame':['text/html','<iframe title="view" src="/" style="width:400px;height:500px"></iframe><button id="side">Outside view</button>'],
 '/frame-export':['text/html','<iframe title="view" src="/export" style="width:400px;height:500px"></iframe><button id="side">Outside view</button>'],
 '/export':['text/html',exported],
 '/':['text/html',html],
 '/react.js':['text/javascript',fs.readFileSync(path.join(runtime,'react.production.min.js'))],
 '/react-dom.js':['text/javascript',fs.readFileSync(path.join(runtime,'react-dom.production.min.js'))],
 '/inspector.js':['text/javascript',fs.readFileSync(path.join(output,'inspector.js'))],
 '/inspector-copy.js':['text/javascript',fs.readFileSync(path.join(output,'inspector.js'))],
 '/inspector.css':['text/css',fs.readFileSync(path.join(output,'inspector.css'))]
};
(async()=>{
 const server=http.createServer((req,res)=>{
  const route=routes[req.url];if(!route){res.writeHead(404);res.end();return;}
  res.writeHead(200,{'Content-Type':route[0]});res.end(route[1]);
 });
 await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
 const browser=await chromium.launch({headless:true,
  ...(process.env.CC_CHROME_EXECUTABLE?{executablePath:process.env.CC_CHROME_EXECUTABLE}:{})});
 const results=[];
 try {
  for(const mode of ['duplicate','native','export'])
  for(const theme of ['light','dark','forced']) for(const width of [280,480,960]) {
   const page=await browser.newPage({viewport:{width,height:700},
    colorScheme:theme==='dark'?'dark':'light',forcedColors:theme==='forced'?'active':'none'});
   const errors=[];page.on('pageerror',e=>errors.push(e.message));
   await page.goto(`http://127.0.0.1:${server.address().port}/${mode==='native'?'':mode}`);
   const first=page.getByRole('button',{name:'Outside interface',exact:true});
   const second=page.getByRole('button',{name:'Inside interface',exact:true});
   const open=page.locator('.cc-inspector-body:popover-open');
   const empty=page.locator('#empty'), outside=page.locator('#outside');
   const closed=()=>page.waitForFunction(()=>!document.querySelector(':popover-open'),
    {},{timeout:1500});
   // Hover previews survive the small gap into the panel, then disappear on departure.
   await first.hover(); assert.equal(await open.count(),1);
   await open.hover(); await page.waitForTimeout(220);
   assert.equal(await open.count(),1);
   await empty.hover(); await closed();
   // A pointer click and the focus it leaves behind must not pin the preview.
   await first.click(); assert.equal(await first.getAttribute('aria-pressed'),'false');
   await empty.hover(); await closed();
   // Only a deliberate double-click pins. Other hovers do not replace that pin.
   await first.dblclick(); assert.equal(await first.getAttribute('aria-pressed'),'true');
   await empty.hover(); await page.waitForTimeout(220); assert.equal(await open.count(),1);
   await first.dblclick(); assert.equal(await first.getAttribute('aria-pressed'),'false');
   await empty.hover(); await closed();
   await first.dblclick();
   await second.hover(); assert.equal(await open.getAttribute('aria-label'),'Outside interface');
   await empty.click(); await closed();
   await page.waitForTimeout(220); assert.equal(await open.count(),0,'empty-space click reopened it');
   for(let i=0;i<4;i++) {
    await first.dblclick(); await second.click();
    assert.equal(await open.count(),1);
    assert.equal(await open.getAttribute('aria-label'),'Inside interface');
    assert.equal(await first.getAttribute('aria-expanded'),'false');
    await open.getByRole('button',{name:'Close information'}).click();
    assert.equal(await open.count(),0);
    assert(await second.evaluate(e=>document.activeElement===e));
   }
   // Tab previews; Enter/Space pin; Escape closes without reopening on restored focus.
   await outside.focus(); await page.keyboard.press('Tab');
   assert.equal(await first.getAttribute('aria-expanded'),'true');
   await page.keyboard.press('Enter');
   assert.equal(await first.getAttribute('aria-pressed'),'true');
   await empty.hover(); await page.waitForTimeout(220); assert.equal(await open.count(),1);
   await page.keyboard.press('Escape'); assert.equal(await open.count(),0);
   assert(await first.evaluate(e=>document.activeElement===e));
   await outside.focus(); await page.keyboard.press('Tab');
   await page.keyboard.press('Space');
   assert.equal(await first.getAttribute('aria-pressed'),'true');
   await open.getByRole('button',{name:'Close information'}).focus();
   await page.keyboard.press('Escape'); assert.equal(await open.count(),0);
   // Changing the Lean object must not retain a pin from the previous object.
   if(mode!=='export') {
    await first.dblclick(); await page.evaluate(()=>window.changeIdentity()); await closed();
   }
   // Interacting with source text also remains transient unless explicitly pinned.
   await second.click(); await open.locator('summary').click();
   await empty.hover(); await closed();
   await second.dblclick();
   if(await open.locator('details').getAttribute('open')!==null) await open.locator('summary').click();
   const compact=await open.boundingBox();
   assert(compact.width<=280,'short native popover is unnecessarily wide');
   await open.locator('summary').click();
   await page.waitForFunction(()=>{
    const b=document.querySelector(':popover-open').getBoundingClientRect();
    return b.left>=0&&b.top>=0&&b.right<=innerWidth&&b.bottom<=innerHeight;
   });
   const expanded=await open.boundingBox();
   const anchor=await second.boundingBox();
   assert(expanded.y>=anchor.y+anchor.height || expanded.y+expanded.height<=anchor.y,
    'the expanded inspector covers its own double-click trigger');
   if(width>=480) assert(expanded.width>compact.width,'native source disclosure did not grow');
   await open.locator('summary').click();
   assert(Math.abs((await open.boundingBox()).width-compact.width)<=1,
    'native popover did not shrink when source closed');
   await open.locator('summary').click();
   assert.equal(await second.getAttribute('aria-expanded'),'true');
   await page.setViewportSize({width:280,height:400});
   await page.waitForFunction(()=>{
    const b=document.querySelector(':popover-open').getBoundingClientRect();
    return b.left>=0&&b.top>=0&&b.right<=innerWidth&&b.bottom<=innerHeight;
   });
   await open.getByRole('button',{name:'Close information'}).click();
   assert.equal(await open.count(),0);
   assert.deepEqual(errors,[],`popover lifecycle errors at ${theme}/${width}`);
   results.push({mode,theme,width,passed:true});await page.close();
  }
  for(const mode of ['native','export']) {
   const page=await browser.newPage({viewport:{width:900,height:700}});
   const errors=[];page.on('pageerror',e=>errors.push(e.message));
   await page.goto(`http://127.0.0.1:${server.address().port}/frame${mode==='export'?'-export':''}`);
   const frame=page.frameLocator('iframe');
   const trigger=frame.getByRole('button',{name:'Outside interface',exact:true});
   await trigger.hover();
   assert.equal(await frame.locator(':popover-open').count(),1);
   await page.locator('#side').hover();
   await page.waitForFunction(()=>!document.querySelector('iframe').contentDocument
    .querySelector(':popover-open'),{},{timeout:1500});
   await trigger.dblclick(); await page.locator('#side').hover();
   await page.waitForTimeout(220); assert.equal(await frame.locator(':popover-open').count(),1);
   await page.locator('#side').click();
   await page.waitForFunction(()=>!document.querySelector('iframe').contentDocument
    .querySelector(':popover-open'),{},{timeout:1500});
   assert.deepEqual(errors,[]);results.push({mode,iframeExit:true,passed:true});await page.close();
  }
  fs.writeFileSync(path.join(output,'inspector-results.json'),JSON.stringify(results,null,2));
  console.log('27 native/export/duplicate-module width/theme combinations and 2 iframe-exit cases: hover, double-click pin, empty-space dismissal, keyboard, switching and resize passed.');
 } finally {await browser.close();await new Promise(resolve=>server.close(resolve));}
})().catch(e=>{console.error(e);process.exitCode=1;});
