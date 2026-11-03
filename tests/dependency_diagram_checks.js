const assert = require('node:assert/strict');
const vm = require('node:vm');
const fs = require('node:fs');
const popupTimers = new Map(); let nextPopupTimer = 0;
global.setTimeout = fn => {const id=++nextPopupTimer;popupTimers.set(id,fn);return id;};
global.clearTimeout = id => popupTimers.delete(id);
function runPopupTimers(){const pending=[...popupTimers.values()];popupTimers.clear();pending.forEach(fn=>fn());}
class Element {
  constructor(tagName) { const classes=new Set(); this.classList={add:c=>classes.add(c),remove:c=>classes.delete(c),contains:c=>classes.has(c)}; this.tagName = tagName; this.children = []; this.style = {}; this.attrs = {}; this.events = {}; this.dataset = {scope:'file'}; this.value = 'all'; this.clientWidth = 1000; this.clientHeight = 550; this.parentElement = {classList:{toggle(){}},append(){}}; }
  setAttribute(k,v) { this.attrs[k] = v; }
  append(e) { this.children.push(e); }
  contains(e) { return e === this || this.children.some(child=>child.contains(e)); }
  replaceChildren() { this.children = []; }
  addEventListener(k,fn) { this.events[k] = fn; }
  getBoundingClientRect() { return {left:0,top:0,width:this.clientWidth,height:this.clientHeight}; }
  setPointerCapture() {}
  focus() { this.focused = true; }
  matches() { return this.focusVisible !== false; }
  cloneNode(deep) {
    const copy=new Element(this.tagName); copy.attrs={...this.attrs}; copy.style={...this.style}; copy.textContent=this.textContent;
    if (deep) copy.children=this.children.map(child=>child.cloneNode(true));
    return copy;
  }
  getBBox() {
    const boxes=this.children.filter(e=>e.tagName==='text').map(e=> {
      const size=Number(e.attrs.style.match(/font-size:([0-9.]+)px/)[1]), width=e.textContent.length*size*.6;
      return {x:-width/2,y:Number(e.attrs.y)-size*.85,width,height:size};
    });
    if (!boxes.length) return {x:0,y:0,width:0,height:0};
    const x=Math.min(...boxes.map(b=>b.x)), y=Math.min(...boxes.map(b=>b.y));
    return {x,y,width:Math.max(...boxes.map(b=>b.x+b.width))-x,height:Math.max(...boxes.map(b=>b.y+b.height))-y};
  }
}
function fixture(n) {
  return Object.fromEntries(Array.from({length:n},(_,i) => ['n'+i,{name:'n'+i,file:'A.v',kind:'lemma',href:'#n'+i,explanation:{status:'available',description:'Explanation for n'+i+'.'},dependencies:i ? ['n'+(i-1)] : []}]));
}
const elements = new Map();
const get = id => { if (!elements.has(id)) elements.set(id,new Element()); return elements.get(id); };
get('dependency-data').textContent = JSON.stringify(fixture(100));
const panel = new Element('section');
global.document = {events:{},body:new Element('body'),addEventListener(k,fn){this.events[k]=fn;},getElementById:get,querySelector:()=>{panel.dataset.scope=global.scope || 'file';return panel;},createElement:tag=>new Element(tag),createElementNS:(ns,tag)=>new Element(tag)};
global.ResizeObserver = class { constructor(fn) { global.resize = fn; } observe(){} };
let frozenPoints = new WeakMap();
global.checkFixed = (fixed,points) => {
  if (!frozenPoints.has(fixed)) frozenPoints.set(fixed,new Map());
  const saved = frozenPoints.get(fixed);
  for (const [id,p] of saved) assert.deepEqual(points[id],p,'a fixed node moved during later-tier placement');
  for (const id of fixed) if (!saved.has(id)) saved.set(id,{...points[id]});
};
const script = fs.readFileSync(0,'utf8');
vm.runInThisContext(script);
const {importance,layout,tiers} = graph;
// Placement must stay outside the node, including corners, narrow viewports,
// long explanations and circles whose centres are slightly off screen.
for (const [w,h] of [[1000,550],[320,550],[240,240],[1000,240],[100,100]]) {
  for (const x of [-5,12,w/2,w-12,w+5]) for (const y of [-5,12,h/2,h-12,h+5]) {
    const radius=14, dw=Math.min(420,w-24), dh=Math.min(360,h-24);
    const r=graph.popupPlacement(x,y,radius,dw,dh,w,h);
    assert.ok(r);
    const bw=Math.min(dw,r.w), bh=Math.min(dh,r.h);
    const left=Math.max(r.x,Math.min(x-bw/2,r.x+r.w-bw));
    const top=Math.max(r.y,Math.min(y-bh/2,r.y+r.h-bh));
    assert.ok(left>=0 && top>=0 && left+bw<=w+1e-8 && top+bh<=h+1e-8);
    assert.ok(left>=x+radius+10-1e-8 || left+bw<=x-radius-10+1e-8 || top>=y+radius+10-1e-8 || top+bh<=y-radius-10+1e-8,'popup overlaps its node');
  }
}
assert.ok(graph.popupPlacement(500,530,14,420,300,1000,550).y<530,'bottom nodes place the popup above');
const close = (a,b) => assert.ok(Math.abs(a-b) < 1e-8, `${a} != ${b}`);
const chain = importance(['a','b','c'],[['a','b'],['b','c']]);
assert.ok(chain.edges[0] > chain.edges[1]);
assert.ok(chain.nodes.get('a') > chain.nodes.get('b'));
assert.ok(chain.nodes.get('b') > chain.nodes.get('c'));
close(chain.edges.reduce((a,b)=>a+b,0),1);
close([...chain.nodes.values()].reduce((a,b)=>a+b,0),1);
for (const edges of [[['a','a']],[['a','b'],['b','a']],[]]) {
  const result = importance(['a','b','isolated'],edges);
  assert.ok(result.nodes.get('isolated') > 0);
  close([...result.nodes.values()].reduce((a,b)=>a+b,0),1);
}
assert.equal(importance([],[]).nodes.size,0);
// Compare the optimized junction calculation with an explicitly constructed
// directed line graph on branching and cyclic topology.
const topology = [['a','b'],['a','c'],['b','c'],['c','b'],['c','c']];
let expected = Array(topology.length).fill(1/topology.length);
for (let iteration=0;iteration<100;iteration++) {
  const next = Array(topology.length).fill(.15/topology.length);
  topology.forEach(([target],i)=> {
    const successors = topology.map(([,source],j)=>source===target ? j : -1).filter(j=>j>=0);
    const destinations = successors.length ? successors : topology.map((_,j)=>j);
    for (const j of destinations) next[j] += .85*expected[i]/destinations.length;
  });
  const change=next.reduce((sum,value,i)=>sum+Math.abs(value-expected[i]),0);
  expected=next; if (change<1e-8) break;
}
importance(['a','b','c'],topology).edges.forEach((value,i)=>close(value,expected[i]));

const tied = tiers(Array.from({length:100},(_,i)=>i),()=>1,String);
assert.ok([...tied.values()].every(t=>t===0));
const scores = tiers(Array.from({length:100},(_,i)=>i),i=>100-i,String);
assert.equal(scores.get(23),0); assert.equal(scores.get(24),1); assert.equal(scores.get(48),2);
const nodes = fixture(100), edges = Object.keys(nodes).flatMap(id=>nodes[id].dependencies.map(other=>[id,other]));
const first = layout(nodes,edges), second = layout(nodes,edges);
assert.deepEqual(first.points,second.points);
for (const [id,p] of Object.entries(first.points)) {
  for (const [other,q] of Object.entries(first.points)) if (id !== other) assert.ok(Math.abs(p.x-q.x)>=220 || Math.abs(p.y-q.y)>=90, `${id} overlaps ${other}`);
}
let state = graph.state();
const before = JSON.stringify(state.drawing.points);
for (const [id,node] of state.drawing.nodeElements) {
  assert.equal(node.children.filter(e=>e.tagName==='circle').length,1);
  assert.equal(node.children.filter(e=>e.tagName==='rect').length,0);
  const label=state.drawing.labels.get(id);
  assert.ok(label.group.children.every(e=>Number(e.attrs.y)>0));
  assert.ok(label.fontSize>=11 && label.fontSize<=20);
}
const fontOnScreen = id => {
  const state=graph.state(), label=state.drawing.labels.get(id);
  const compensation=Number(label.group.attrs.transform.match(/scale\(([^)]+)\)/)[1]);
  const screenScale=Math.min(get('dependency-svg').clientWidth/state.viewport.width,get('dependency-svg').clientHeight/state.viewport.height);
  return label.fontSize*compensation*screenScale;
};
const fontsBefore=new Map([...state.drawing.labels.keys()].map(id=>[id,fontOnScreen(id)]));
assert.ok(fontOnScreen('n99')>fontOnScreen('n0'));
const suppressed=[...state.drawing.labels].filter(([,label])=>label.suppressed);
assert.ok(suppressed.length>0,'dense views suppress overlapping labels');
const [suppressedId,suppressedLabel]=suppressed[0];
assert.equal(state.drawing.nodeElements.get(suppressedId).style.display,'');
for(const [id,label] of state.drawing.labels) {
  const transform=label.group.attrs.transform.match(/translate\(([^,]+),([^)]+)\) scale\(([^)]+)\)/);
  close(Number(transform[1]),110);
  close((Number(transform[2])-45)/Number(transform[3]),state.drawing.nodeRadii.get(id));
  assert.ok(!state.drawing.nodeElements.get(id).children.some(e=>e.tagName==='path'),'no label connector paths');
}
const hiddenTransform=suppressedLabel.group.attrs.transform;
state.drawing.nodeCircles.get(suppressedId).events.pointerenter();
assert.equal(state.drawing.popup.style.display,'');
assert.equal(state.drawing.popup.children[0].tagName,'strong');
assert.equal(state.drawing.popup.children[1].textContent,'AI-generated explanation');
assert.equal(state.drawing.popup.children[2].textContent,'Explanation for '+suppressedId+'.');
assert.equal(state.drawing.popup.attrs.role,'dialog');
assert.equal(state.drawing.popup.children[3].tagName,'a');
assert.equal(state.drawing.popup.children[3].attrs.href,state.drawing.nodes[suppressedId].href);
assert.equal(state.drawing.popup.children[3].textContent,'Open declaration');
assert.equal(suppressedLabel.group.style.display,'none');
assert.equal(state.drawing.nodeElements.get(suppressedId).style.display,'');
assert.equal(suppressedLabel.group.attrs.transform,hiddenTransform);
state.drawing.nodeCircles.get(suppressedId).events.pointerleave();
assert.equal(state.drawing.popup.style.display,'');
state.drawing.popup.events.pointerenter(); runPopupTimers(); assert.equal(state.drawing.popup.style.display,'');
let stopped=false; state.drawing.popup.events.wheel({stopPropagation(){stopped=true;}}); assert.ok(stopped);
state.drawing.popup.events.pointerleave(); runPopupTimers(); assert.equal(state.drawing.popup.style.display,'none');
state.drawing.nodeElements.get(suppressedId).events.focus(); assert.equal(state.drawing.popup.style.display,'');
const popupLink=state.drawing.popup.children[3];
state.drawing.nodeElements.get(suppressedId).events.blur({relatedTarget:popupLink});
state.drawing.popup.events.focusin(); runPopupTimers(); assert.equal(state.drawing.popup.style.display,'');
state.drawing.popup.events.focusout({relatedTarget:null}); assert.equal(state.drawing.popup.style.display,'none');
state.drawing.nodeElements.get(suppressedId).events.focus();
state.drawing.nodeElements.get(suppressedId).events.blur(); assert.equal(state.drawing.popup.style.display,'none');
state.drawing.nodeElements.get(suppressedId).focusVisible=false;
state.drawing.nodeElements.get(suppressedId).events.focus(); assert.equal(state.drawing.popup.style.display,'none');
state.drawing.nodeElements.get(suppressedId).focusVisible=true;
const visibleLabelId=[...state.drawing.labels].find(([,label])=>label.onScreen&&!label.suppressed)[0];
state.drawing.nodeCircles.get(visibleLabelId).events.pointerenter(); assert.equal(state.drawing.popup.style.display,'');
assert.equal(state.drawing.popup.children[2].textContent,'Explanation for '+visibleLabelId+'.');
state.drawing.nodeCircles.get(visibleLabelId).events.pointerleave(); runPopupTimers();

const radiusOnScreen = id => {
  const state=graph.state(), scale=Math.min(get('dependency-svg').clientWidth/state.viewport.width,get('dependency-svg').clientHeight/state.viewport.height);
  return Number(state.drawing.nodeCircles.get(id).attrs.r)*scale;
};
const arrowOnScreen = i => {
  const state=graph.state(), scale=Math.min(get('dependency-svg').clientWidth/state.viewport.width,get('dependency-svg').clientHeight/state.viewport.height);
  return Number(state.drawing.edgeMarkers[i].attrs.markerWidth)*scale;
};
const radiiBefore=new Map([...state.drawing.nodeCircles.keys()].map(id=>[id,radiusOnScreen(id)]));
const arrowsBefore=state.drawing.edgeMarkers.map((_,i)=>arrowOnScreen(i));
const widthsBefore=[...state.drawing.edgeWidths];
close(radiusOnScreen('n99')**2/radiusOnScreen('n0')**2,state.drawing.ranks.nodes.get('n99')/state.drawing.ranks.nodes.get('n0'));
close(Math.min(...widthsBefore),1.5);
close(Math.max(...widthsBefore),5);
const minEdgeScore=Math.min(...state.drawing.ranks.edges), maxEdgeScore=Math.max(...state.drawing.ranks.edges);
widthsBefore.forEach((width,i)=>close((width-1.5)/3.5,(state.drawing.ranks.edges[i]-minEdgeScore)/(maxEdgeScore-minEdgeScore)));
for (const [i,edge] of state.drawing.edgeElements.entries()) {
  assert.equal(edge.attrs['vector-effect'],'non-scaling-stroke');
  close(Number(edge.attrs.style.match(/stroke-width:([0-9.e+-]+)px/)[1]),widthsBefore[i]);
}

const screenLabels = [];
for (const [id,{group}] of state.drawing.labels) {
  if (group.style.display === 'none') continue;
  const match=group.attrs.transform.match(/translate\(([^,]+),([^)]+)\) scale\(([^)]+)\)/), box=group.getBBox();
  const units=Number(match[3]), scale=Math.min(get('dependency-svg').clientWidth/state.viewport.width,get('dependency-svg').clientHeight/state.viewport.height);
  screenLabels.push({id,x:(state.drawing.points[id].x+Number(match[1])+box.x*units-state.viewport.x)*scale,y:(state.drawing.points[id].y+Number(match[2])+box.y*units-state.viewport.y)*scale,w:box.width,h:box.height});
}
for (let i=0;i<screenLabels.length;i++) for(let j=i+1;j<screenLabels.length;j++) {
  const a=screenLabels[i],b=screenLabels[j];
  assert.ok(!(a.x<b.x+b.w && a.x+a.w>b.x && a.y<b.y+b.h && a.y+a.h>b.y),'overview labels overlap: '+JSON.stringify([a,b]));
}


// Every suppressed label overlaps a retained label with greater importance
// (or deterministic tie precedence), rather than causing its node to disappear.
for (const [id,label] of suppressed) {
  const match=label.group.attrs.transform.match(/translate\(([^,]+),([^)]+)\) scale\(([^)]+)\)/), box=label.group.getBBox();
  const units=Number(match[3]), scale=Math.min(get('dependency-svg').clientWidth/state.viewport.width,get('dependency-svg').clientHeight/state.viewport.height);
  const a={x:(state.drawing.points[id].x+Number(match[1])+box.x*units-state.viewport.x)*scale,y:(state.drawing.points[id].y+Number(match[2])+box.y*units-state.viewport.y)*scale,w:box.width,h:box.height};
  const winner=screenLabels.find(b=>a.x-4<b.x+b.w+4&&a.x+a.w+4>b.x-4&&a.y-4<b.y+b.h+4&&a.y+a.h+4>b.y-4&&state.drawing.ranks.nodes.get(b.id)>=state.drawing.ranks.nodes.get(id));
  assert.ok(winner,'suppressed label has a visible collision winner');
  assert.ok(state.drawing.ranks.nodes.get(winner.id)>=state.drawing.ranks.nodes.get(id));
  assert.equal(state.drawing.nodeElements.get(id).style.display,'');
}

const visible = () => [...graph.state().drawing.nodeElements].filter(([,e])=>e.style.display !== 'none').map(([id])=>id);
assert.ok(visible().length < 100);
let singleEndpoint = false;
for (let i=0;i<15;i++) {
  graph.zoom(.8); state = graph.state();
  const shown = new Set(visible());
  state.drawing.edgeElements.forEach((e,index)=> {
    const [a,b] = state.drawing.edges[index];
    const expected = state.drawing.edgeTiers.get(index)<=state.currentTier && (shown.has(a)||shown.has(b));
    assert.equal(e.style.display !== 'none',expected);
    if (expected && shown.has(a)!==shown.has(b)) singleEndpoint=true;
  });
}
assert.ok(singleEndpoint,'a high-ranked edge reaches a hidden endpoint');
assert.equal(visible().length,100);
for (const [id,size] of fontsBefore) close(fontOnScreen(id),size);
for (const [id,size] of radiiBefore) close(radiusOnScreen(id),size);
for (const [i,size] of arrowsBefore.entries()) close(arrowOnScreen(i),size);
assert.deepEqual(graph.state().drawing.edgeWidths,widthsBefore);
for(const [id,label] of graph.state().drawing.labels) {
  const transform=label.group.attrs.transform.match(/translate\(([^,]+),([^)]+)\) scale\(([^)]+)\)/);
  close(Number(transform[1]),110);
  close((Number(transform[2])-45)/Number(transform[3]),graph.state().drawing.nodeRadii.get(id));
}

assert.equal(JSON.stringify(graph.state().drawing.points),before);
graph.fit(); assert.ok(visible().length<100);
const svg = get('dependency-svg');
const centerBefore = {...graph.state().viewport};
svg.events.keydown({key:'ArrowRight',preventDefault(){}});
assert.ok(graph.state().viewport.x > centerBefore.x);
svg.events.keydown({key:'+',preventDefault(){}});
assert.ok(graph.state().viewport.width < centerBefore.width);
svg.events.wheel({deltaY:-1,clientX:100,clientY:150,preventDefault(){}});
const beforeDrag={...graph.state().viewport};
svg.events.pointerdown({button:0,target:{closest:()=>null},clientX:100,clientY:100,pointerId:1});
svg.events.pointermove({clientX:160,clientY:140});
assert.ok(graph.state().viewport.x < beforeDrag.x);
svg.events.pointerup();
assert.equal(JSON.stringify(graph.state().drawing.points),before);
svg.events.keydown({key:'0',preventDefault(){}});
assert.equal(graph.state().currentTier,0);

resize(); const oldTier=graph.state().currentTier;
get('dependency-svg').clientWidth=500; resize();
assert.equal(graph.state().currentTier,oldTier);
for (const [id,size] of fontsBefore) close(fontOnScreen(id),size);
for (const [id,size] of radiiBefore) close(radiusOnScreen(id),size);
for (const [i,size] of arrowsBefore.entries()) close(arrowOnScreen(i),size);
assert.deepEqual(graph.state().drawing.edgeWidths,widthsBefore);
for(const [id,label] of graph.state().drawing.labels) {
  const transform=label.group.attrs.transform.match(/translate\(([^,]+),([^)]+)\) scale\(([^)]+)\)/);
  close(Number(transform[1]),110);
  close((Number(transform[2])-45)/Number(transform[3]),graph.state().drawing.nodeRadii.get(id));
}

assert.equal(JSON.stringify(graph.state().drawing.points),before);
graph.search.value='n40'; graph.search.events.input();
assert.equal(visible().length,3);
for (const id of visible()) close(radiusOnScreen(id),radiiBefore.get(id));
assert.equal(JSON.stringify(graph.state().drawing.points),before);
graph.mode.value='files'; graph.render(); assert.equal(visible().length,1);
graph.mode.value='all'; graph.render(); assert.equal(JSON.stringify(graph.state().drawing.points),before);
get('dependency-data').textContent=JSON.stringify(fixture(6)); vm.runInThisContext(script);
assert.equal(visible().length,6); assert.equal(graph.state().drawing.edgeElements.filter(e=>e.style.display!=='none').length,5);
// Dependency endpoints meet circle boundaries at the current camera scale.
state=graph.state();
for (let i=0;i<state.drawing.edges.length;i++) {
  const [a,b]=state.drawing.edges[i], edge=state.drawing.edgeElements[i], path=edge.attrs.d;
  if (!path) continue;
  const coordinates=path.match(/-?[0-9]+(?:\.[0-9]+)?(?:e[+-]?[0-9]+)?/g).map(Number);
  const start=state.drawing.points[a], end=state.drawing.points[b];
  close(Math.hypot(coordinates[0]-start.x-110,coordinates[1]-start.y-45),Number(state.drawing.nodeCircles.get(a).attrs.r));
  close(Math.hypot(coordinates.at(-2)-end.x-110,coordinates.at(-1)-end.y-45),Number(state.drawing.nodeCircles.get(b).attrs.r));
}
const recursive=fixture(3); recursive.n0.dependencies=['n0']; recursive.n1.dependencies=['n2']; recursive.n2.dependencies=['n1'];
get('dependency-data').textContent=JSON.stringify(recursive); vm.runInThisContext(script);
graph.state().drawing.edgeWidths.forEach(width=>close(width,5));
const selfIndex=graph.state().drawing.edges.findIndex(([a,b])=>a===b);
assert.ok(graph.state().drawing.edgeElements[selfIndex].attrs.d.includes(' C '));
const recursiveRadii=new Map([...graph.state().drawing.nodeRadii].map(([id])=>[id,radiusOnScreen(id)]));
const recursiveArrows=graph.state().drawing.edgeMarkers.map((_,i)=>arrowOnScreen(i));
graph.zoom(.8);
for(const [id,r] of recursiveRadii)close(radiusOnScreen(id),r);
recursiveArrows.forEach((r,i)=>close(arrowOnScreen(i),r));
const unavailable=fixture(1); unavailable.n0.explanation={};
get('dependency-data').textContent=JSON.stringify(unavailable); vm.runInThisContext(script);
graph.state().drawing.nodeCircles.get('n0').events.pointerenter();
assert.equal(graph.state().drawing.popup.children[2].textContent,'No AI-generated explanation is available for this declaration.');
graph.state().drawing.nodeCircles.get('n0').events.pointerleave();runPopupTimers();
get('dependency-data').textContent='{}'; vm.runInThisContext(script); assert.equal(visible().length,0);
const grouped=fixture(100);
for (const [id,node] of Object.entries(grouped)) node.file='file'+Math.floor(Number(id.slice(1))/2)+'.v';
get('dependency-data').textContent=JSON.stringify(grouped);
get('graph-view').value='files'; global.scope='project'; vm.runInThisContext(script);
assert.equal(Object.keys(graph.state().drawing.nodes).length,50);
assert.equal(graph.state().drawing.edges.length,49);
const fileNode=[...graph.state().drawing.labels].find(([,label])=>label.onScreen)[0];
graph.state().drawing.nodeCircles.get(fileNode).events.pointerenter();
assert.ok(graph.state().drawing.popup.children[2].textContent.includes('Choose All declarations'));
assert.equal(graph.state().drawing.popup.children[3].textContent,'Open file');
assert.equal(graph.state().drawing.popup.children[3].attrs.href,graph.state().drawing.nodes[fileNode].href);
graph.state().drawing.nodeCircles.get(fileNode).events.pointerleave(); runPopupTimers();
assert.ok(visible().length<50);
const filePoints=JSON.stringify(graph.state().drawing.points);
graph.mode.value='all'; graph.render();
const declarationPoints=JSON.stringify(graph.state().drawing.points);
graph.search.value='n40'; graph.search.events.input();
assert.equal(JSON.stringify(graph.state().drawing.points),declarationPoints);
graph.mode.value='files'; graph.render();
assert.equal(JSON.stringify(graph.state().drawing.points),filePoints);
// Main contracts are promoted even when their structural PageRank is low.
const contracts=fixture(100);
for(const node of Object.values(contracts)) node.statement_dependencies=[...node.dependencies];
contracts.n0.dependencies=['n2','n90']; contracts.n0.statement_dependencies=['n2'];
contracts.n1.dependencies=['n3','n0']; contracts.n1.statement_dependencies=['n3'];
for(const id of ['n0','n1']) {contracts[id].main_contract=true;contracts[id].contract={main:true,related:['n2','n3'],representations:['n3']};}
get('dependency-data').textContent=JSON.stringify(contracts); get('graph-view').value='files'; global.scope='project'; vm.runInThisContext(script);
assert.equal(graph.mode.value,'contracts','project graphs default to main contracts when available');
assert.ok(panel.classList.contains('graph-contract-view'));
let contractState=graph.state();
assert.deepEqual(Object.keys(contractState.drawing.nodes).sort(),['n0','n1','n2','n3']);
assert.ok(!contractState.drawing.edges.some(([a,b])=>a==='n0'&&b==='n90'),'proof-only dependencies stay outside the contract view');
assert.equal(contractState.drawing.nodeCircles.get('n0').attrs.fill,'#fff1c2');
assert.equal(contractState.drawing.nodeCircles.get('n3').attrs.stroke,'#29897d');
const contractRank=contractState.drawing.ranks.nodes.get('n0');
close(contractRank,contractState.drawing.ranks.nodes.get('n1'));
assert.ok([...contractState.drawing.ranks.nodes].every(([id,r])=>['n0','n1'].includes(id)||r<contractRank));
assert.equal(contractState.drawing.nodeTiers.get('n0'),0); assert.equal(contractState.drawing.nodeTiers.get('n1'),0);
close(contractState.drawing.labels.get('n0').fontSize,20);
const contractPositions=JSON.stringify(contractState.drawing.points);
graph.mode.value='all'; graph.render();
assert.equal(JSON.stringify(graph.state().drawing.points),contractPositions,'view changes preserve the full graph layout');
assert.equal(graph.state().drawing.nodeCircles.get('n0').attrs.fill,'#fff1c2');
assert.ok(!panel.classList.contains('graph-contract-view'));
graph.zoom(1.25);assert.equal(graph.state().drawing.nodeElements.get('n0').style.display,'');
const contractEdges=Object.keys(contracts).sort().flatMap(id=>contracts[id].dependencies.map(other=>[id,other]));
assert.deepEqual(graph.state().drawing.ranks.edges,importance(Object.keys(contracts).sort(),contractEdges).edges,'priority does not alter edge PageRank');
get('graph-view').value='all';global.scope='file';vm.runInThisContext(script);
assert.equal(graph.mode.value,'all','local pages retain their all-declarations view');
contracts.n0.contract.related=Object.keys(contracts).filter(id=>id!=='n90');
get('dependency-data').textContent=JSON.stringify(contracts);get('graph-view').value='contracts';global.scope='project';vm.runInThisContext(script);
assert.equal(Object.keys(graph.state().drawing.nodes).length,99);
assert.equal([...graph.state().drawing.nodeElements.values()].filter(node=>node.style.display!=='none').length,99,'the focused contract view shows all selected bridge nodes');
get('graph-view').value='files';global.scope='project';
const large=fixture(1000), largeEdges=Object.keys(large).flatMap(id=>large[id].dependencies.map(other=>[id,other]));
const start=performance.now();
const largeLayout=layout(large,largeEdges);
assert.equal(Object.keys(largeLayout.points).length,1000);
assert.ok(Object.values(largeLayout.points).every(p=>Number.isFinite(p.x)&&Number.isFinite(p.y)));
console.log('Graph behavior checks passed; 1000-node layout took '+Math.round(performance.now()-start)+'ms.');

(async () => {
  const button=get('graph-fullscreen'), positions=JSON.stringify(graph.state().drawing.points);
  document.body.style.overflow='auto';
  await button.events.click();
  assert.ok(panel.classList.contains('graph-expanded'));
  assert.equal(button.textContent,'Exit full screen'); assert.equal(button.attrs['aria-pressed'],'true');
  assert.equal(document.body.style.overflow,'hidden');
  const tier=graph.state().currentTier, v={...graph.state().viewport};
  get('dependency-svg').clientWidth=1200; get('dependency-svg').clientHeight=800; resize();
  assert.equal(graph.state().currentTier,tier);
  close(graph.state().viewport.x+graph.state().viewport.width/2,v.x+v.width/2);
  close(graph.state().viewport.y+graph.state().viewport.height/2,v.y+v.height/2);
  assert.equal(JSON.stringify(graph.state().drawing.points),positions);
  document.events.keydown({key:'Escape',preventDefault(){}});
  assert.ok(!panel.classList.contains('graph-expanded'));
  assert.equal(button.textContent,'Full screen'); assert.equal(button.attrs['aria-pressed'],'false');
  assert.equal(document.body.style.overflow,'auto'); assert.ok(button.focused);
  await button.events.click(); await button.events.click();
  assert.ok(!panel.classList.contains('graph-expanded'));
  panel.requestFullscreen=async()=>{document.fullscreenElement=panel;document.events.fullscreenchange();};
  document.exitFullscreen=async()=>{document.fullscreenElement=null;document.events.fullscreenchange();};
  await button.events.click(); assert.equal(document.fullscreenElement,panel); assert.equal(button.attrs['aria-pressed'],'true');
  await button.events.click(); assert.equal(document.fullscreenElement,null); assert.equal(button.attrs['aria-pressed'],'false');
  await button.events.click(); document.events.keydown({key:'Escape',preventDefault(){}}); await Promise.resolve();
  assert.equal(document.fullscreenElement,null); assert.equal(button.attrs['aria-pressed'],'false');
  panel.requestFullscreen=async()=>{throw new Error('Fullscreen unavailable in this browser');};
  await button.events.click(); assert.ok(panel.classList.contains('graph-expanded'));
  document.events.keydown({key:'Escape',preventDefault(){}});
  assert.ok(!panel.classList.contains('graph-expanded'));
  console.log('Fullscreen entry, exit, Escape, fallback, and view preservation passed.');
})().catch(error=>{console.error(error);process.exitCode=1;});
