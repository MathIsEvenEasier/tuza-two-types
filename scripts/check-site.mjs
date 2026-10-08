import assert from 'node:assert/strict';
import {graphFor,cutCover,packing,checkWitness,edge,triangleEdges,matchingColors,sumClasses,presets} from '../docs/model.js';
let cases=0,sufficient=0;
for(const preset of Object.keys(presets))for(let p=1;p<=4;p++)for(let q=1;q<=4;q++){
 const g=graphFor(preset,p,q),P=packing(g),C=cutCover(g),result=checkWitness(g,P,C);cases++;sufficient+=result.witnessesSuffice;
 // Independent check: every unselected edge crosses the full cut.
 for(const[a,b]of g.edges)if(!C.edges.has(edge(a,b)))assert.notEqual(C.side[a],C.side[b]);
 assert.equal(new Set(P.flatMap(triangleEdges)).size,3*P.length);
}
for(let s=2;s<=8;s++){
 const classes=matchingColors(s),all=new Set();assert.equal(classes.length,s%2?s:s-1);
 for(const matching of classes){assert.equal(matching.length,Math.floor(s/2));assert.equal(new Set(matching.flat()).size,2*matching.length);for(const[a,b]of matching){assert(a>=0&&a<s&&b>=0&&b<s&&a!==b);assert(!all.has(edge(a,b)));all.add(edge(a,b));}}
 assert.equal(all.size,s*(s-1)/2);
}
for(const group of sumClasses()){assert.equal(new Set(group.flatMap(triangleEdges)).size,3*group.length);}
// Negative controls: duplicated packed triangle and empty cover must be rejected.
const g=graphFor();assert.throws(()=>checkWitness(g,[g.triangles[0],g.triangles[0]],cutCover(g)));assert.throws(()=>checkWitness(g,[],{edges:new Set()}));
console.log(`Checked ${cases} displayed graphs; ${sufficient} have witnesses proving the factor-two comparison. Matching classes, sum classes and negative controls passed.`);
