import {graphFor,cutCover,packing,checkWitness,edge,triangleEdges,matchingColors,sumClasses} from './model.js';
const $=id=>document.getElementById(id),colors=['#226fa0','#ac4829','#655598','#187d64','#a87512','#914676','#486c3a','#975345','#367b8a','#605245','#595db0','#a7385e','#426a60','#af612a','#767020','#4c6595'];
const NS='http://www.w3.org/2000/svg';
function el(tag,attrs={},text){const e=document.createElementNS(NS,tag);for(const[k,v]of Object.entries(attrs))e.setAttribute(k,v);if(text!==undefined)e.textContent=text;return e;}
function label(x,y,text,attrs={}){return el('text',{x,y,'text-anchor':'middle','dominant-baseline':'central',...attrs},text);}
function circlePositions(n,cx=250,cy=165,r=123){return Array.from({length:n},(_,i)=>{const a=-Math.PI/2+2*Math.PI*i/n;return[cx+r*Math.cos(a),cy+r*Math.sin(a)];});}
function line(points,a,b,attrs={}){return el('line',{x1:points[a][0],y1:points[a][1],x2:points[b][0],y2:points[b][1],...attrs});}
let g,P,C,state,mode='packing',focused=-1;
function updateGraph(){
 g=graphFor($('preset').value,+$('p').value,+$('q').value);P=packing(g);C=cutCover(g);state=checkWitness(g,P,C);focused=-1;$('remove-cover').checked=false;
 $('p-value').textContent=g.p;$('q-value').textContent=g.q;
 $('sets').textContent=`K = {0, 1, 2, 3, 4, 5}. S = {${g.S.join(', ')}}. T = {${g.T.join(', ')}}.`;
 $('packing-count').textContent=P.length;$('cover-count').textContent=C.edges.size;
 $('chain').textContent=state.witnessesSuffice?`τ△ ≤ ${C.edges.size} ≤ ${2*P.length} = 2 × ${P.length} ≤ 2ν△`:`ν△ ≥ ${P.length} and τ△ ≤ ${C.edges.size}`;
 $('witness-note').textContent=state.witnessesSuffice?'The cover has at most twice as many edges as the packing has triangles, which proves the inequality for this graph.':'These particular witnesses do not suffice for the factor-two comparison. The general Lean theorem still covers this graph; the browser construction is only an illustration.';
 drawGraph();
}
function drawGraph(){
 const canvas=$('graph-drawing');canvas.replaceChildren();
 const mobile=matchMedia('(max-width:740px)').matches,cx=mobile?180:360,cy=mobile?190:224;
 $('graph').setAttribute('viewBox',mobile?'0 0 360 380':'0 0 720 460');
 const core=circlePositions(6,cx,cy,mobile?101:133),points=[...core];
 for(let i=0;i<g.p;i++)points.push([mobile?23:70,cy+(i-(g.p-1)/2)*(mobile?75:88)]);
 for(let i=0;i<g.q;i++)points.push([mobile?337:650,cy+(i-(g.q-1)/2)*(mobile?75:88)]);
 canvas.append(el('ellipse',{cx,cy,rx:mobile?128:172,ry:mobile?140:171,fill:'#edf1e7',stroke:'#cdd5c9','stroke-dasharray':'4 5'}));
 canvas.append(label(cx,23,'CLIQUE K',{'font-size':mobile?9:11,'letter-spacing':mobile?0:2}),label(mobile?28:70,23,'TYPE S',{'font-size':mobile?9:11,'letter-spacing':mobile?0:2}),label(mobile?332:650,23,'TYPE T',{'font-size':mobile?9:11,'letter-spacing':mobile?0:2}));
 const edgeColor=new Map();P.forEach((t,i)=>triangleEdges(t).forEach(e=>edgeColor.set(e,i)));
 const sorted=[...g.edges].sort(([a,b],[c,d])=>Number(edgeColor.has(edge(a,b)))-Number(edgeColor.has(edge(c,d))));
 for(const[a,b]of sorted){const key=edge(a,b),index=edgeColor.get(key),hit=C.edges.has(key);if(mode==='cover'&&$('remove-cover').checked&&hit)continue;
  let stroke='#bcc7bd',width=1.3,opacity=.65;
  if(mode==='packing'&&index!==undefined){stroke=colors[index%colors.length];width=focused===-1?3:focused===index?5:1.2;opacity=focused===-1||focused===index?.9:.15;}
  if(mode==='cover'){stroke=hit?'#a54829':'#c4cec3';width=hit?4:1.2;opacity=hit?.95:.7;}
  canvas.append(line(points,a,b,{stroke,'stroke-width':width,opacity}));
 }
 if(mode==='packing'&&focused>=0){const t=P[focused];canvas.append(el('polygon',{points:t.map(i=>points[i].join(',')).join(' '),fill:colors[focused%colors.length],'fill-opacity':.12,stroke:colors[focused%colors.length],'stroke-width':4}));}
 points.forEach(([x,y],i)=>{const inS=g.S.includes(i),inT=g.T.includes(i);let fill=i<6?(inS&&inT?'#7e659d':inS?'#287ab0':inT?'#bd602e':'#8b9485'):i<g.k+g.p?'#287ab0':'#bd602e';
  canvas.append(el('circle',{cx:x,cy:y,r:i<6?18:16,fill,stroke:mode==='cover'?(C.side[i]?'#183d3a':'#fffaf3'):'#fffaf3','stroke-width':mode==='cover'?4:2}));
  const name=i<6?String(i):i<6+g.p?'S'+(i-5):'T'+(i-5-g.p);canvas.append(label(x,y,name,{'font-size':i<6?14:11,style:'fill:white','font-weight':'bold'}));
 });
 const captions={structure:`${g.n} vertices, ${g.edges.length} edges, ${g.triangles.length} triangles. Outside vertices of type S and T are independent; all six clique vertices are pairwise adjacent.`,packing:focused<0?`${P.length} triangles, each with its own edge color. They may share vertices; no edge is reused. Use the arrows to isolate one triangle.`:`Triangle ${focused+1}: vertices ${P[focused].map(i=>i<6?i:i<6+g.p?'S'+(i-5):'T'+(i-5-g.p)).join(', ')}. Its three edges appear in no other packed triangle.`,cover:$('remove-cover').checked?'The selected edges are removed. Every remaining edge crosses the cut, so no triangle can remain.':`${C.edges.size} rust-colored edges meet all ${g.triangles.length} triangles. Light and dark node outlines show the two sides of the cut. Remove these edges to see the triangle-free remainder.`};
 $('graph-caption').textContent=captions[mode];$('graph-description').textContent=captions[mode];
 for(const b of document.querySelectorAll('[data-mode]'))b.setAttribute('aria-pressed',String(b.dataset.mode===mode));
 for(const id of ['step-back','step-forward','step-label','show-all'])$(id).hidden=mode!=='packing';$('remove-label').hidden=mode!=='cover';
 $('step-label').textContent=focused<0?'All triangles':`${focused+1} / ${P.length}`;$('show-all').disabled=focused<0;
}
for(const id of ['preset','p','q'])$(id).addEventListener('input',updateGraph);
for(const b of document.querySelectorAll('[data-mode]'))b.addEventListener('click',()=>{mode=b.dataset.mode;drawGraph();});
$('reset').addEventListener('click',()=>{$('preset').value='crossing';$('p').value=2;$('q').value=2;mode='packing';updateGraph();});
$('step-forward').addEventListener('click',()=>{focused=(focused+1)%P.length;drawGraph();});
$('step-back').addEventListener('click',()=>{focused=focused<0?P.length-1:(focused+P.length-1)%P.length;drawGraph();});
$('show-all').addEventListener('click',()=>{focused=-1;drawGraph();});$('remove-cover').addEventListener('change',drawGraph);
const repo='https://github.com/MathIsEvenEasier/tuza-two-types/blob/main/';
const proof={
 compression:{title:'Cap the number of twin vertices',formula:'m → min(m, h(s))',body:'A proper edge coloring lets us move the centers of any packed triangles onto at most h(s) twins, without changing their core edges or the other packed triangles. A separate replacement argument preserves covers. Apply the reduction to both types.',role:'Arbitrary multiplicities become bounded parameters. The original graph and the compressed graph have exactly the same two optima.',name:'TuzaGraphTransfer.compress_both_types',file:'formal/GraphReductions.lean#L4243',next:'See the matching-color construction below ↓',href:'#matching'},
 packing:{title:'Construct compatible triangle packings',formula:'a feasible packing ⇒ L ≤ ν△',body:'Matching colors supply triangles at outside centers. The two neighborhood types may compete for the same core edges, so independent and coupled selections control this overlap. Greedy completion adds unused core triangles; Mantel’s theorem bounds the residue. Sum-coloring supplies further lower bounds.',role:'We obtain several valid lower bounds. Their strengths differ across the parameter domain, so the comparison can choose among them.',name:'TuzaPackingInterfaces.outside_and_completion',file:'formal/GraphReductions.lean#L4371',next:'Explore the sum-coloring lemma ↓',href:'#sum-colors'},
 covers:{title:'Every triangle must meet the cut cover.',formula:'τ△ ≤ U for every constructed cover',body:'Edges within either side of a cut meet all clique triangles. Suitable spokes or shadow edges also meet all triangles at outside vertices. The proof uses several cuts, including an unbalanced cut through S ∩ T. Rounding is part of the formal argument.',role:'These constructions give upper bounds for the actual cover optimum. A different cut may be best in a different region.',name:'TuzaCutCovers.two_type_cover_bound',file:'formal/GraphReductions.lean#L2646',next:'Inspect an actual cut cover ↑',href:'#explore'},
 normalization:{title:'Compare cover and packing bounds',formula:'τ△ ≤ U ≤ 2L ≤ 2ν△',body:'The bridge proves that the scalar cover expressions bound the actual cover number and the packing expressions bound the actual packing number. For large k, dividing by k² yields expressions in six normalized variables. Lean proves these identities from the graph definitions.',role:'A certificate proves U ≤ 2L. The two graph bounds then give τ△ ≤ 2ν△.',name:'TuzaNormalizedGraph.conclusion_implies_tuza',file:'formal/NormalizedBounds.lean#L390',next:'See why all large k fit ↓',href:'#all-sizes'},
 finite:{title:'Exhaust the bounded parameter domain.',formula:'2 ≤ k ≤ 42',body:'With multiplicities capped and symmetric parameters ordered, the remaining range contains 23,848,371 parameter tuples. Generated Lean proofs check the required comparison and join the ranges. The final quantified result is TuzaFiniteData.all_checked.',role:'Lean checks each generated proof and the lemmas that combine the ranges. Together they establish the comparison for every tuple in the finite domain.',name:'TuzaFinalAssembly.finite_ordered',file:'formal/NormalizedBounds.lean#L486',next:'Download every certificate source ↗',href:'https://github.com/MathIsEvenEasier/tuza-two-types/releases/tag/v1.0.0'},
 interval:{title:'Prove a whole real domain.',formula:'0 ≤ ρ = 1/k ≤ 1/43',body:'Analytic lemmas cover several ranges for large cliques. For the rest, exact interval arithmetic proves the required comparison throughout each certified box. Proved contraction, splitting and joining rules cover the constrained domain with 178,506 leaves.',role:'Every graph with k ≥ 43 that remains after the analytic reductions maps into this domain.',name:'TuzaFinalAssembly.continuous_ordered',file:'formal/NormalizedBounds.lean#L517',next:'Inspect the normalization ↓',href:'#all-sizes'},
 result:{title:'Assemble the final theorem',formula:'τ△(G) ≤ 2ν△(G)',body:'Handle clique sizes below two directly, discard inactive outside vertices, classify the remaining neighborhoods, and preserve both optima through compression. Apply the finite certificate for 2 ≤ k ≤ 42 and the interval certificate for k ≥ 43.',role:'The resulting theorem quantifies over every finite split graph with at most two active neighborhood types.',name:'TuzaTwoTypes.tuza_of_two_active_types',file:'formal/Result.lean#L17',next:'Inspect verification evidence ↓',href:'#verify'}
};
function showProof(key){const d=proof[key];$('proof-detail').innerHTML=`<p class="eyebrow">Role in the proof</p><h3>${d.title}</h3><p>${d.body}</p><div class="formula">${d.formula}</div><p class="detail-role">${d.role}</p><p class="small">Exact declaration</p><a href="${repo+d.file}"><code>${d.name}</code></a><p style="margin-top:25px;margin-bottom:0"><a href="${d.href}">${d.next}</a></p>`;for(const b of document.querySelectorAll('[data-proof]')){b.classList.toggle('selected',b.dataset.proof===key);b.setAttribute('aria-pressed',String(b.dataset.proof===key));}}
for(const b of document.querySelectorAll('[data-proof]'))b.addEventListener('click',()=>showProof(b.dataset.proof));
let matchingColor=0;
function drawMatching(){const s=+$('s-size').value,m=+$('copies').value,classes=matchingColors(s),h=classes.length,r=Math.min(m,h),withCenter=$('show-center').checked,assigned=matchingColor%h<r,points=circlePositions(s,withCenter?195:250,165,withCenter?108:122),svg=$('matching-svg');matchingColor%=h;svg.replaceChildren();
 const groups=new Map();classes.forEach((list,i)=>list.forEach(([a,b])=>groups.set(edge(a,b),i)));
 for(let a=0;a<s;a++)for(let b=a+1;b<s;b++){const c=groups.get(edge(a,b));svg.append(line(points,a,b,{stroke:c===matchingColor?colors[c]:'#d9ded4','stroke-width':c===matchingColor?5:1.3}));}
 if(withCenter&&assigned){
  const center=[445,165],all=[...points,center],selected=classes[matchingColor];
  for(let a=0;a<s;a++)svg.append(line(all,a,s,{stroke:'#d9ded4','stroke-width':1}));
  for(const[a,b]of selected){svg.append(el('polygon',{points:[points[a],points[b],center].map(p=>p.join(',')).join(' '),fill:colors[matchingColor],'fill-opacity':.055,stroke:colors[matchingColor],'stroke-width':2.5}));}
  svg.append(el('circle',{cx:445,cy:165,r:22,fill:colors[matchingColor],stroke:'#fffcf7','stroke-width':2}),label(445,165,'x'+(matchingColor+1),{'font-size':16,style:'fill:white'}));
  svg.append(label(445,206,'CENTER',{'font-size':10}));
 }
 points.forEach(([x,y],i)=>{svg.append(el('circle',{cx:x,cy:y,r:18,fill:'#193e3b',stroke:'#fffcf7','stroke-width':2}),label(x,y,i,{'font-size':13,style:'fill:white'}));});
 svg.append(label(250,332,`Color ${matchingColor+1}: ${classes[matchingColor].map(e=>e.join('–')).join(', ')}${withCenter&&!assigned?' · no center assigned':''}`,{'font-size':12}));
 $('color-buttons').replaceChildren();classes.forEach((_,i)=>{const b=document.createElement('button');b.textContent=i+1;b.setAttribute('aria-label',`Show matching color ${i+1}`);b.setAttribute('aria-pressed',String(i===matchingColor));b.style.borderColor=colors[i];b.addEventListener('click',()=>{matchingColor=i;drawMatching();});$('color-buttons').append(b);});
 $('s-size-value').textContent=s;$('copies-value').textContent=m;
 $('matching-formula').innerHTML=`h(${s}) = ${h}<br>${r} colors × ${Math.floor(s/2)} edges = <strong>${r*Math.floor(s/2)} triangles</strong>`;
 $('matching-explanation').textContent=`Each color is a matching of ${Math.floor(s/2)} edges. With ${m} available twin${m===1?'':'s'}, assign ${r} color${r===1?'':'s'} to ${r} distinct center${r===1?'':'s'}.${m>h?' The extra twins are unnecessary for this construction.':''} This counts constructed triangles using outside centers; triangles entirely inside the core may add more.`;
}
for(const id of ['s-size','copies','show-center'])$(id).addEventListener('input',drawMatching);
let sumColor=0;const classes=sumClasses();
function drawSum(){const svg=$('sum-svg'),points=circlePositions(6,250,165,117);svg.replaceChildren();
 for(let a=0;a<6;a++)for(let b=a+1;b<6;b++)svg.append(line(points,a,b,{stroke:'#d7dfd3','stroke-width':1}));
 classes[sumColor].forEach((t,i)=>{svg.append(el('polygon',{points:t.map(v=>points[v].join(',')).join(' '),fill:colors[sumColor],'fill-opacity':.07,stroke:colors[sumColor],'stroke-width':3}));});
 points.forEach(([x,y],i)=>{svg.append(el('circle',{cx:x,cy:y,r:17,fill:'#193e3b',stroke:'#fffcf7','stroke-width':2}),label(x,y,i,{'font-size':13,style:'fill:white'}));});
 $('sum-caption').textContent=`Sum ${sumColor} modulo 6: ${classes[sumColor].length} edge-disjoint triangles — ${classes[sumColor].map(t=>'{'+t.join(', ')+'}').join(', ')}.`;
 for(const b of $('sum-buttons').children)b.setAttribute('aria-pressed',String(+b.dataset.sum===sumColor));
}
for(let c=0;c<6;c++){const b=document.createElement('button');b.textContent='Σ '+c;b.dataset.sum=c;b.setAttribute('aria-label',`Show sum ${c} modulo six`);b.addEventListener('click',()=>{sumColor=c;drawSum();});$('sum-buttons').append(b);}
function drawRho(){const k=+$('large-k').value;if(!Number.isInteger(k)||k<43||k>1000000){$('large-k').setCustomValidity('Choose an integer from 43 to 1,000,000.');$('rho-text').textContent='Choose an integer from 43 to 1,000,000 for this display.';return;}$('large-k').setCustomValidity('');$('rho-dot').style.left=(4300/k)+'%';$('rho-text').textContent=`k = ${k.toLocaleString('en-US')} gives ρ = 1/${k.toLocaleString('en-US')} ≈ ${(1/k).toPrecision(5)}. This value is inside [0, 1/43]. The theorem itself has no upper bound on k.`;}
$('large-k').addEventListener('input',drawRho);for(const b of document.querySelectorAll('[data-k]'))b.addEventListener('click',()=>{$('large-k').value=b.dataset.k;drawRho();});
updateGraph();showProof('compression');drawMatching();drawSum();drawRho();

matchMedia('(max-width:740px)').addEventListener('change',drawGraph);
