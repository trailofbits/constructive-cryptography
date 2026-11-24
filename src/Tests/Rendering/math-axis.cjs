// Browser-side measurements shared by the proof and system galleries.
module.exports = function mathAxisFailures() {
 const failures=[];
 const rect=e=>e.getBoundingClientRect();
 const cy=e=>{const r=rect(e);return r.top+r.height/2;};
 const aligned=(a,b,reason)=>{
  if(Math.abs(cy(a)-cy(b))>1)
   failures.push({reason,left:a.className,right:b.className,delta:cy(a)-cy(b)});
 };
 for(const system of document.querySelectorAll('.cc-system')) {
  const body=system.querySelector(':scope > .cc-system-body');
  if(!body) {failures.push({reason:'system has no body alignment anchor'});continue;}
  aligned(system,body,'interface labels displaced the system body');
 }
 for(const distance of document.querySelectorAll('.cc-distance')) {
  const operator=distance.querySelector(':scope > .cc-operator');
  const operands=distance.querySelector(':scope > .cc-operands');
  if(!operator||!operands) continue;
  const bodies=[...operands.querySelectorAll(':scope > .cc-system > .cc-system-body')];
  // Wrapped operands occupy separate rows. Otherwise all notation shares their axis.
  if(bodies.length!==2 || Math.min(...bodies.map(e=>rect(e).bottom))<=
    Math.max(...bodies.map(e=>rect(e).top))) continue;
  for(const e of [...bodies,...distance.querySelectorAll(':scope > .cc-delimiter'),
    ...operands.querySelectorAll(':scope > .cc-comma')])
   aligned(operator,e,'distance notation is off the diagram axis');
 }
 for(const comparison of document.querySelectorAll('.cc-comparison')) {
  const systems=[...comparison.querySelectorAll(':scope > .cc-system')];
  const relation=comparison.querySelector(':scope > .cc-relation');
  if(systems.length!==2||!relation) continue;
  const [left,right]=systems.map(rect), r=rect(relation);
  if(left.bottom<=right.top && (r.top<left.bottom-1||r.bottom>right.top+1))
   failures.push({reason:'relation sits beside a stacked operand instead of between operands'});
 }
 for(const tail of document.querySelectorAll('.cc-comparison-tail')) {
  const relation=tail.querySelector(':scope > .cc-relation');
  const literal=tail.querySelector(':scope > .cc-cards > .cc-literal:only-child');
  if(relation&&literal&&!relation.querySelector('.cc-protocol'))
   aligned(relation,literal,'relation and bound split across rows');
 }
 for(const footer of document.querySelectorAll('.cc-step-footer')) {
  const source=footer.querySelector(':scope > .cc-source-toggle > summary');
  const method=footer.querySelector(':scope > .cc-proof-method .cc-inspector-trigger');
  if(source&&method) aligned(source,method,'source and method controls are misaligned');
 }
 return failures;
};
