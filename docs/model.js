export const presets={
 crossing:{S:[0,1,2,3],T:[2,3,4,5]},
 nested:{S:[1,2,3],T:[0,1,2,3,4]},
 disjoint:{S:[0,1,2],T:[3,4,5]},
 wide:{S:[0,1,2,3,4],T:[1,2,3,4,5]}
};
export const edge=(a,b)=>a<b?`${a}-${b}`:`${b}-${a}`;
export const triangleEdges=t=>[edge(t[0],t[1]),edge(t[0],t[2]),edge(t[1],t[2])];
export function graphFor(preset='crossing',p=2,q=2){
 if(!presets[preset]||![p,q].every(n=>Number.isInteger(n)&&n>=1&&n<=4))throw Error('Invalid example');
 const {S,T}=presets[preset],k=6,n=k+p+q,edges=[];
 for(let a=0;a<k;a++)for(let b=a+1;b<k;b++)edges.push([a,b]);
 for(let x=k;x<n;x++)for(const a of x<k+p?S:T)edges.push([a,x]);
 const adjacency=new Set(edges.map(([a,b])=>edge(a,b))),triangles=[];
 for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)for(let c=b+1;c<n;c++)if([edge(a,b),edge(a,c),edge(b,c)].every(e=>adjacency.has(e)))triangles.push([a,b,c]);
 return {k,n,p,q,S,T,edges,triangles,adjacency};
}
export function cutCover(g){
 let best=null;
 for(let mask=0;mask<(1<<g.k);mask++){
  const side=Array.from({length:g.k},(_,i)=>(mask>>i)&1),chosen=new Set();
  for(const [a,b]of g.edges)if(b<g.k&&side[a]===side[b])chosen.add(edge(a,b));
  for(let x=g.k;x<g.n;x++){
   const N=x<g.k+g.p?g.S:g.T,groups=[N.filter(a=>side[a]===0),N.filter(a=>side[a]===1)];
   const small=groups[0].length<=groups[1].length?groups[0]:groups[1];
   for(const a of small)chosen.add(edge(a,x));
   side[x]=small===groups[0]?0:1;
  }
  if(!best||chosen.size<best.edges.size)best={edges:chosen,side};
 }
 return best;
}
export function packing(g){
 const tri=g.triangles.map((t,i)=>({t,i,edges:triangleEdges(t)}));let best=[];
 for(let seed=0;seed<48;seed++){
  let rng=seed+1;const random=()=>{rng=(Math.imul(rng,1664525)+1013904223)>>>0;return rng/4294967296;};
  const ordered=tri.map(t=>({...t,rank:random()}));
  if(seed===0)ordered.sort((a,b)=>(b.t[2]>=g.k)-(a.t[2]>=g.k)||a.i-b.i);
  else ordered.sort((a,b)=>a.rank-b.rank);
  const used=new Set(),current=[];
  for(const item of ordered)if(item.edges.every(e=>!used.has(e))){current.push(item.t);item.edges.forEach(e=>used.add(e));}
  if(current.length>best.length)best=current;
 }
 // The formal sum-coloring lemma gives another feasible starting packing.
 for(let color=0;color<g.n;color++){
  const current=g.triangles.filter(t=>t.reduce((a,b)=>a+b,0)%g.n===color),used=new Set(current.flatMap(triangleEdges));
  for(const item of tri)if(item.edges.every(e=>!used.has(e))){current.push(item.t);item.edges.forEach(e=>used.add(e));}
  if(current.length>best.length)best=current;
 }
 return best;
}
export function checkWitness(g,P,C){
 const used=new Set();
 for(const t of P){if(new Set(t).size!==3)throw Error('Invalid triangle');for(const e of triangleEdges(t)){if(!g.adjacency.has(e)||used.has(e))throw Error('Packing conflict');used.add(e);}}
 if([...C.edges].some(e=>!g.adjacency.has(e)))throw Error('Cover contains a non-edge');
 const missed=g.triangles.filter(t=>!triangleEdges(t).some(e=>C.edges.has(e)));
 if(missed.length)throw Error('Uncovered triangle');
 return {packing:P.length,cover:C.edges.size,triangles:g.triangles.length,witnessesSuffice:C.edges.size<=2*P.length};
}
export function matchingColors(s){
 const size=s%2===0?s:s+1,m=size-1,classes=Array.from({length:m},()=>[]);
 for(let c=0;c<m;c++){
  const pairs=[[m,c]];
  for(let i=1;i<=(m-1)/2;i++)pairs.push([(c+i)%m,(c-i+m)%m]);
  classes[c]=pairs.filter(([a,b])=>a<s&&b<s);
 }
 return classes;
}
export function sumClasses(n=6){
 const classes=Array.from({length:n},()=>[]);
 for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)for(let c=b+1;c<n;c++)classes[(a+b+c)%n].push([a,b,c]);
 return classes;
}
