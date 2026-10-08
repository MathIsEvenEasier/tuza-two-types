import GraphReductions
import CertificateKernel

open Finset
set_option maxRecDepth 200000
set_option maxHeartbeats 80000000


/-! The arithmetic expressions have these explicit real meanings. -/
namespace TuzaExpressionValues
open TuzaInterval TuzaCertificate TuzaCertificateExpressions TuzaSeparableCover TuzaCutFormulas

noncomputable def coverValues (v : Point) : List ℝ :=
  let x := v 0; let y := v 1; let w := v 2
  let p := v 3; let q := v 4; let r := v 5; let m := p+q
  [p*penalty 1 x+q*penalty 1 y,
   1/4-r^2/4-y*(1-y)+min (w*max 0 (x-w)) (x^2/4),
   p*(x-1/2)+q*(y-1/2)-m^2/4+(max 0 ((1+m)/2-w))^2,
   costOne 1 x y w p q,costTwo 1 x y w p q,
   costThree 1 x y w p q,costFour 1 x y w p q]

noncomputable def i0 (v : Point) : ℝ := v 3*v 0+v 4*v 1-v 3*v 4*(v 2)^2/(v 0*v 1)
noncomputable def i1 (v : Point) : ℝ := v 3+v 4-v 3*v 4*v 2/(v 0*v 1)
noncomputable def j0 (v : Point) : ℝ :=
  (v 3*(v 0)^2+v 4*(v 1)^2-max 0 (v 3+v 4-v 1)*(v 2)^2)/v 1
noncomputable def j1 (v : Point) : ℝ :=
  (v 3*v 0+v 4*v 1-max 0 (v 3+v 4-v 1)*v 2)/v 1
noncomputable def outsideValue (v : Point) (base loss : ℝ) : ℝ :=
  base-1/4+v 5*(1/2-loss)-(v 5)^2/4
noncomputable def completionValue (v : Point) (base loss : ℝ) : ℝ :=
  -1/12+2*base/3+v 5*(1/6-2*loss/3)-(v 5)^2/4
noncomputable def averageValue (v : Point) (p q : ℝ) : ℝ :=
  (1/12+p*((v 0)^2-1/4)+q*((v 1)^2-1/4)+
    v 5*(-1/2+p*(1/2-v 0)+q*(1/2-v 1))+
    (v 5)^2*(5/12-(p+q)/4))/(1+p+q)
noncomputable def packingValues (v : Point) : List ℝ :=
  [1/12-v 5/2+5*(v 5)^2/12,
   outsideValue v (i0 v) (i1 v),completionValue v (i0 v) (i1 v),
   outsideValue v (j0 v) (j1 v),completionValue v (j0 v) (j1 v),
   averageValue v (v 3) (v 4),averageValue v (v 3) 0,averageValue v 0 (v 4)]

theorem val_add (v : Point) (a b : Expr 6) : value v (a+b) = value v a+value v b := rfl
theorem val_neg (v : Point) (a : Expr 6) : value v (-a) = -value v a := rfl
theorem val_sub (v : Point) (a b : Expr 6) : value v (a-b) = value v a-value v b := by
  change value v a+(-value v b) = value v a-value v b
  ring
theorem val_mul (v : Point) (a b : Expr 6) : value v (a*b) = value v a*value v b := rfl
theorem val_div (v : Point) (a b : Expr 6) : value v (a/b) = value v a/value v b := by
  change value v a*(1/value v b) = value v a/value v b
  ring
theorem val_nat (v : Point) (n : ℕ) : value v (OfNat.ofNat n : Expr 6) = (n : ℝ) := by
  change ((n : ℚ) : ℝ) = (n : ℝ)
  norm_cast

set_option maxHeartbeats 800000 in
theorem covers_value (v : Point) : coverCosts.map (value v) = coverValues v := by
  norm_num [coverCosts,coverValues,costOne,costTwo,costThree,costFour,penalty,
    TuzaCertificateExpressions.x,TuzaCertificateExpressions.y,TuzaCertificateExpressions.w,
    TuzaCertificateExpressions.p,TuzaCertificateExpressions.q,TuzaCertificateExpressions.rho,
    TuzaCertificateExpressions.m,half,quarter,rat,TuzaCertificateExpressions.f,TuzaCertificateExpressions.pos,TuzaCertificateExpressions.sq,excess,val_add,val_neg,val_sub,val_mul,val_div,val_nat,value,pow_two,div_eq_mul_inv,max_assoc,add_assoc,mul_assoc,sub_eq_add_neg]

set_option maxHeartbeats 800000 in
theorem packings_value (v : Point) : packingGaps.map (value v) = packingValues v := by
  norm_num [packingGaps,packingValues,outsideGap,completionGap,averageGap,
    outsideValue,completionValue,averageValue,i0,i1,j0,j1,
    TuzaCertificateExpressions.i0,TuzaCertificateExpressions.i1,
    TuzaCertificateExpressions.j0,TuzaCertificateExpressions.j1,
    TuzaCertificateExpressions.x,TuzaCertificateExpressions.y,TuzaCertificateExpressions.w,
    TuzaCertificateExpressions.p,TuzaCertificateExpressions.q,TuzaCertificateExpressions.rho,
    TuzaCertificateExpressions.m,half,quarter,rat,TuzaCertificateExpressions.pos,TuzaCertificateExpressions.sq,val_add,val_neg,val_sub,val_mul,val_div,val_nat,value,pow_two,div_eq_mul_inv,add_assoc,mul_assoc,sub_eq_add_neg]

theorem common_value (v : Point) : value v common =
    (1+3*(v 3+v 4)^2)/16-(1+v 3+v 4)*(max 0 ((1+v 3+v 4)/2-v 2))^2 := by
  norm_num [common,excess,TuzaCertificateExpressions.m,TuzaCertificateExpressions.p,
    TuzaCertificateExpressions.q,TuzaCertificateExpressions.w,TuzaCertificateExpressions.pos,TuzaCertificateExpressions.sq,val_add,val_neg,val_sub,val_mul,val_div,val_nat,value,pow_two,div_eq_mul_inv,add_assoc,mul_assoc,sub_eq_add_neg]

noncomputable def cup (v : Point) : ℝ := (1-v 5)^2/4

theorem conclusion_from_bounds (v : Point) (tau nu : ℝ)
    (hcover : ∀ c ∈ coverValues v, tau ≤ cup v+c)
    (hpacking : ∀ b ∈ packingValues v, cup v+b ≤ nu)
    (hcommon : 0 ≤ (1+3*(v 3+v 4)^2)/16-
      (1+v 3+v 4)*(max 0 ((1+v 3+v 4)/2-v 2))^2 → tau ≤ nu)
    (h : Conclusion v) : tau ≤ nu := by
  rcases h with h | ⟨a,ha,b,hb,hab⟩
  · apply hcommon
    rwa [common_value] at h
  · have ha' : value v a ∈ coverValues v := by
      rw [← covers_value]
      exact List.mem_map.mpr ⟨a,ha,rfl⟩
    have hb' : value v b ∈ packingValues v := by
      rw [← packings_value]
      exact List.mem_map.mpr ⟨b,hb,rfl⟩
    exact (hcover _ ha').trans ((add_le_add_right hab _).trans (hpacking _ hb'))

#print axioms covers_value
#print axioms packings_value
#print axioms common_value
#print axioms conclusion_from_bounds
#check conclusion_from_bounds
end TuzaExpressionValues

/-! Exact normalization identities; no numerical approximation is used. -/
namespace TuzaNormalization
open TuzaCertificate TuzaExpressionValues TuzaSeparableCover TuzaCutFormulas
  TuzaHomogeneity TuzaPackingInterfaces TuzaCommonRounding

noncomputable def point (k s t u p q : ℝ) : Point := fun i => match i.val with
  | 0 => s/k | 1 => t/k | 2 => u/k | 3 => p/k | 4 => q/k | _ => 1/k

@[simp] theorem point_0 (k s t u p q : ℝ) : point k s t u p q 0 = s/k := rfl
@[simp] theorem point_1 (k s t u p q : ℝ) : point k s t u p q 1 = t/k := rfl
@[simp] theorem point_2 (k s t u p q : ℝ) : point k s t u p q 2 = u/k := rfl
@[simp] theorem point_3 (k s t u p q : ℝ) : point k s t u p q 3 = p/k := rfl
@[simp] theorem point_4 (k s t u p q : ℝ) : point k s t u p q 4 = q/k := rfl
@[simp] theorem point_5 (k s t u p q : ℝ) : point k s t u p q 5 = 1/k := rfl

theorem rescale (k a : ℝ) (hk : k ≠ 0) : k*(a/k) = a := by field_simp

theorem rescale_pos (k a : ℝ) (hk : 0 < k) : k*max 0 (a/k) = max 0 a := by
  rw [← scale_pos hk.le,rescale k a hk.ne']

theorem cup_identity (k s t u p q : ℝ) (hk : k ≠ 0) :
    k^2*cup (point k s t u p q) = (k-1)^2/4 := by
  simp only [cup,point_0,point_1,point_2,point_3,point_4,point_5]
  field_simp [hk]
  <;> ring

theorem separable_identity (k s t u p q : ℝ) (hk : 0 < k) :
    k^2*((p/k)*penalty 1 (s/k)+(q/k)*penalty 1 (t/k)) =
      p*penalty k s+q*penalty k t := by
  have hs := penalty_scale k (s/k) hk.le
  have ht := penalty_scale k (t/k) hk.le
  rw [rescale k s hk.ne'] at hs
  rw [rescale k t hk.ne'] at ht
  rw [hs,ht]
  field_simp [hk]
  <;> ring

theorem common_identity (k s t u p q : ℝ) (hk : 0 < k) :
    k^2*(cup (point k s t u p q)+(p/k)*(s/k-1/2)+(q/k)*(t/k-1/2)-
      (p/k+q/k)^2/4+(max 0 ((1+p/k+q/k)/2-u/k))^2) =
      k*(k-1)/2+p*s+q*t-(k+p+q)^2/4+(max 0 ((k+p+q)/2-u))^2+1/4 := by
  have he : (1+p/k+q/k)/2-u/k = ((k+p+q)/2-u)/k := by field_simp [hk.ne'] <;> ring
  rw [he]
  have hm := rescale_pos k ((k+p+q)/2-u) hk
  have hm2 : k^2*(max 0 (((k+p+q)/2-u)/k))^2 = (max 0 ((k+p+q)/2-u))^2 := by
    nlinarith only [congrArg (fun a : ℝ => a^2) hm]
  have hbase : k^2*(cup (point k s t u p q)+(p/k)*(s/k-1/2)+(q/k)*(t/k-1/2)-(p/k+q/k)^2/4) =
      k*(k-1)/2+p*s+q*t-(k+p+q)^2/4+1/4 := by
    simp only [cup,point_5]
    field_simp [hk.ne']
    <;> ring
  nlinarith only [hm2,hbase]

theorem shadow_identity (k s t u p q : ℝ) (hk : 0 < k) (hu : 0 ≤ u) (hus : u ≤ s) :
    k^2*(cup (point k s t u p q)+1/4-(1/k)^2/4-(t/k)*(1-t/k)+
      min ((u/k)*max 0 (s/k-u/k)) ((s/k)^2/4)) =
      k*(k-1)/2-t*(k-t)+s*u-u^2 := by
  have hs : 0 ≤ s/k-u/k := sub_nonneg.mpr ((div_le_div_iff_of_pos_right hk).mpr hus)
  rw [max_eq_right hs,min_eq_left (by nlinarith [sq_nonneg (s/k-2*(u/k))])]
  simp only [cup,point_0,point_1,point_2,point_3,point_4,point_5]
  field_simp [hk.ne']
  <;> ring

theorem independent_identity (k : ℝ) (s t u p q : ℕ)
    (hk : k ≠ 0) (hs : (s : ℝ) ≠ 0) (ht : (t : ℝ) ≠ 0) :
    k^2*(i0 (point k s t u p q)-(1/k)*i1 (point k s t u p q)) =
      2*independentRate s t u p q := by
  simp only [i0,i1,point_0,point_1,point_2,point_3,point_4,point_5,independentRate]
  rw [choose_two_real,choose_two_real,choose_two_real]
  field_simp [hk,hs,ht]
  <;> ring

theorem coupled_identity (k : ℝ) (s t u p q : ℕ)
    (hk : 0 < k) (ht : (t : ℝ) ≠ 0) :
    k^2*(j0 (point k s t u p q)-(1/k)*j1 (point k s t u p q)) =
      2*coupledRate s t u p q := by
  simp only [j0,j1,point_0,point_1,point_2,point_3,point_4,point_5,coupledRate]
  rw [choose_two_real,choose_two_real,choose_two_real]
  have he : (p : ℝ)/k+q/k-t/k = ((p : ℝ)+q-t)/k := by ring
  rw [he]
  have hm := rescale_pos k ((p : ℝ)+q-t) hk
  have hm' : max 0 (((p : ℝ)+q-t)/k) = max 0 ((p : ℝ)+q-t)/k := by
    apply (eq_div_iff hk.ne').mpr
    simpa only [mul_comm] using hm
  rw [hm']
  field_simp [hk.ne',ht]
  <;> ring

theorem outside_identity (v : Point) (a b : ℝ) :
    cup v+outsideValue v a b = a-v 5*b := by dsimp [cup,outsideValue]; ring

theorem completion_identity (v : Point) (a b : ℝ) :
    cup v+completionValue v a b = 2*(a-v 5*b)/3+(1-2*v 5)/6 := by
  dsimp [cup,completionValue]; ring

theorem clique_identity (k s t u p q : ℝ) (hk : k ≠ 0) :
    k^2*(cup (point k s t u p q)+1/12-(1/k)/2+5*(1/k)^2/12) =
      (k-1)*(k-2)/3 := by
  simp only [cup,point_0,point_1,point_2,point_3,point_4,point_5]
  field_simp [hk]
  <;> ring

theorem average_identity (k s t u p q r z : ℝ) (hk : k ≠ 0) (hd : k+r+z ≠ 0) :
    k^2*(cup (point k s t u p q)+averageValue (point k s t u p q) (r/k) (z/k)) =
      (k*(k-1)*(k-2)/3+r*s*(s-1)+z*t*(t-1))/(k+r+z) := by
  have hn : 1+r/k+z/k ≠ 0 := by
    have he : 1+r/k+z/k = (k+r+z)/k := by field_simp [hk] <;> ring
    rw [he]
    exact div_ne_zero hd hk
  simp only [cup,averageValue,point_0,point_1,point_2,point_3,point_4,point_5]
  field_simp [hk,hd,hn]
  <;> ring

#print axioms cup_identity
#print axioms separable_identity
#print axioms common_identity
#print axioms shadow_identity
#print axioms independent_identity
#print axioms coupled_identity
#print axioms average_identity
#check average_identity
end TuzaNormalization

/-! Every normalized envelope is backed by a proved graph bound. -/
namespace TuzaNormalizedGraph
open Finset TuzaCompression TuzaGraphCompression TuzaIndependentAllocation
  TuzaCoverCompression TuzaGraphBounds TuzaGraphReductions TuzaRegionCuts
  TuzaPackingInterfaces TuzaBalancedRounding TuzaCommonRounding TuzaSeparableCover
  TuzaCutFormulas TuzaNormalization TuzaExpressionValues TuzaHomogeneity TuzaCertificate
variable {V : Type*} [DecidableEq V] [Fintype V]

theorem cover_bounds (S T : Finset V) (p q : ℕ) (hk : 2 ≤ Fintype.card V)
    (hst : S.card ≤ T.card) (ht : (Fintype.card V : ℝ)/2 ≤ T.card) :
    let k : ℝ := Fintype.card V
    let v := point k S.card T.card (S ∩ T).card p q
    ∀ c ∈ coverValues v,
      (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ)/k^2 ≤ cup v+c := by
  dsimp only
  let k : ℝ := Fintype.card V
  let s : ℝ := S.card
  let t : ℝ := T.card
  let u : ℝ := (S ∩ T).card
  let v := point k s t u p q
  let tau : ℝ := coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q))
  have hk0 : 0 < k := by dsimp [k]; exact_mod_cast (show 0 < Fintype.card V by omega)
  have hk2 : 0 < k^2 := sq_pos_of_pos hk0
  have hc := (coreBudget_bounds (Fintype.card V) hk).2
  have hsep := separable_cover_bound S T p q
  have hshadow := large_shadow S T p q
  have hcommon := common_cover_optimized S T p q
  rw [choose_two_real] at hcommon
  obtain ⟨h1,h2,h3,h4⟩ := four_balanced_bounds S T p q hst ht
  have hscaled (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)
      (hf : tau ≤ (coreBudget (Fintype.card V) : ℝ)+f k s t u p q)
      (he : f k s t u p q = k^2*f 1 (s/k) (t/k) (u/k) (p/k) (q/k)) :
      tau/k^2 ≤ cup v+f 1 (s/k) (t/k) (u/k) (p/k) (q/k) := by
    apply (div_le_iff₀ hk2).mpr
    have hv : k^2*cup v = (k-1)^2/4 := cup_identity k s t u p q hk0.ne'
    rw [he] at hf
    nlinarith only [hf,hc,hv]
  have hscale1 := costOne_scale k (s/k) (t/k) (u/k) ((p : ℝ)/k) ((q : ℝ)/k) hk0.le
  have hscale2 := costTwo_scale k (s/k) (t/k) (u/k) ((p : ℝ)/k) ((q : ℝ)/k) hk0.le
  have hscale3 := costThree_scale k (s/k) (t/k) (u/k) ((p : ℝ)/k) ((q : ℝ)/k) hk0.le
  have hscale4 := costFour_scale k (s/k) (t/k) (u/k) ((p : ℝ)/k) ((q : ℝ)/k) hk0.le
  simp only [rescale k _ hk0.ne'] at hscale1 hscale2 hscale3 hscale4
  intro c hcMem
  change c ∈ coverValues v at hcMem
  change tau/k^2 ≤ cup v+c
  simp only [coverValues,point,List.mem_cons,List.not_mem_nil,or_false] at hcMem
  rcases hcMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply (div_le_iff₀ hk2).mpr
    have hv := cup_identity k s t u p q hk0.ne'
    have he := separable_identity k s t u p q hk0
    change tau ≤ (coreBudget (Fintype.card V) : ℝ)+(p : ℝ)*penalty k s+(q : ℝ)*penalty k t at hsep
    simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]
    nlinarith only [hv,he,hsep,hc]
  · apply (div_le_iff₀ hk2).mpr
    have hu : 0 ≤ u := by dsimp [u]; positivity
    have hus : u ≤ s := by dsimp [u,s]; exact_mod_cast card_le_card (inter_subset_left (s₁ := S) (s₂ := T))
    have he := shadow_identity k s t u p q hk0 hu hus
    rw [choose_two_real] at hshadow
    change tau ≤ k*(k-1)/2-t*(k-t)+s*u-u^2 at hshadow
    simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]
    nlinarith only [he,hshadow]
  · apply (div_le_iff₀ hk2).mpr
    have he := common_identity k s t u p q hk0
    change tau ≤ k*(k-1)/2+(p : ℝ)*s+(q : ℝ)*t-(k+p+q)^2/4+
      (max 0 ((k+p+q)/2-u))^2+1/4 at hcommon
    simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]
    simp only [add_assoc] at he hcommon ⊢
    nlinarith only [he,hcommon]
  · exact hscaled costOne h1 hscale1
  · exact hscaled costTwo h2 hscale2
  · exact hscaled costThree h3 hscale3
  · exact hscaled costFour h4 hscale4

theorem packing_bounds (S T : Finset V) (p q : ℕ) (hk : 2 ≤ Fintype.card V)
    (hs : 2 ≤ S.card) (ht : 2 ≤ T.card) (hst : S.card ≤ T.card)
    (hp : p ≤ colorCount S.card) (hq : q ≤ colorCount T.card) :
    let k : ℝ := Fintype.card V
    let v := point k S.card T.card (S ∩ T).card p q
    ∀ b ∈ packingValues v, cup v+b ≤
      (2*(packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ))/k^2 := by
  dsimp only
  let k : ℝ := Fintype.card V
  let s : ℝ := S.card
  let t : ℝ := T.card
  let u : ℝ := (S ∩ T).card
  let v := point k s t u p q
  let nu : ℝ := packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q))
  have hk0 : 0 < k := by dsimp [k]; exact_mod_cast (show 0 < Fintype.card V by omega)
  have hk2 : 0 < k^2 := sq_pos_of_pos hk0
  have hs0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast (show S.card ≠ 0 by omega)
  have ht0 : (T.card : ℝ) ≠ 0 := by exact_mod_cast (show T.card ≠ 0 by omega)
  let I := independentRate S.card T.card (S ∩ T).card p q
  let J := coupledRate S.card T.card (S ∩ T).card p q
  obtain ⟨hout,hcomp⟩ := outside_and_completion S T hs ht hst p q hp hq
  change max I J ≤ nu at hout
  change 2*max I J+((Fintype.card V).choose 2 : ℝ) ≤
    3*nu+((Fintype.card V^2/4 : ℕ) : ℝ) at hcomp
  have hcoreN := Nat.sub_add_cancel (core_floor_le (Fintype.card V) hk)
  have hcoreR : (coreBudget (Fintype.card V) : ℝ)+((Fintype.card V^2/4 : ℕ) : ℝ) =
      ((Fintype.card V).choose 2 : ℝ) := by exact_mod_cast hcoreN
  have hc := (coreBudget_bounds (Fintype.card V) hk).1
  have hI : I ≤ max I J := le_max_left _ _
  have hJ : J ≤ max I J := le_max_right _ _
  have hi : k^2*(i0 v-v 5*i1 v) = 2*I := independent_identity k _ _ _ _ _ hk0.ne' hs0 ht0
  have hj : k^2*(j0 v-v 5*j1 v) = 2*J := coupled_identity k _ _ _ _ _ hk0 ht0
  have outside (a b L : ℝ) (he : k^2*(a-v 5*b) = 2*L) (hL : L ≤ max I J) :
      cup v+outsideValue v a b ≤ 2*nu/k^2 := by
    apply (le_div_iff₀ hk2).mpr
    rw [outside_identity]
    nlinarith only [he,hL,hout]
  have completion (a b L : ℝ) (he : k^2*(a-v 5*b) = 2*L) (hL : L ≤ max I J) :
      cup v+completionValue v a b ≤ 2*nu/k^2 := by
    apply (le_div_iff₀ hk2).mpr
    rw [completion_identity]
    have hv : k^2*(1-2*v 5) = k*(k-2) := by simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]; field_simp [hk0.ne'] <;> ring
    nlinarith only [he,hL,hcomp,hcoreR,hc,hv]
  have avg (r z : ℕ) (hr : r ≤ p) (hz : z ≤ q) :
      cup v+averageValue v ((r : ℝ)/k) ((z : ℝ)/k) ≤ 2*nu/k^2 := by
    have hn := subgraph_triangle_bound S T r z p q hr hz
    have hR : ((Fintype.card V).choose 3 : ℝ)+(r : ℝ)*S.card.choose 2+(z : ℝ)*T.card.choose 2 ≤
        (k+r+z)*nu := by dsimp only [k,nu]; exact_mod_cast hn
    rw [choose_three_real,choose_two_real,choose_two_real] at hR
    have hd : 0 < k+r+z := by positivity
    have he := average_identity k s t u p q r z hk0.ne' hd.ne'
    apply (le_div_iff₀ hk2).mpr
    rw [mul_comm,he]
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hR]
  intro b hb
  change b ∈ packingValues v at hb
  change cup v+b ≤ 2*nu/k^2
  simp only [packingValues,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply (le_div_iff₀ hk2).mpr
    have he := clique_identity k s t u p q hk0.ne'
    have hh := clique_real S T p q (by omega)
    simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]
    nlinarith only [he,hh]
  · exact outside _ _ I hi hI
  · exact completion _ _ I hi hI
  · exact outside _ _ J hj hJ
  · exact completion _ _ J hj hJ
  · exact avg p q le_rfl le_rfl
  · simpa only [Nat.cast_zero,zero_div,v,point_3,point_4] using avg p 0 le_rfl (Nat.zero_le _)
  · simpa only [Nat.cast_zero,zero_div,v,point_3,point_4] using avg 0 q (Nat.zero_le _) le_rfl

#print axioms cover_bounds
#print axioms packing_bounds
#check packing_bounds
end TuzaNormalizedGraph

namespace TuzaNormalizedGraph
open Finset TuzaCompression TuzaGraphCompression TuzaIndependentAllocation
  TuzaGraphBounds TuzaGraphReductions TuzaRegionCuts TuzaRealBounds TuzaCoverCompression
  TuzaNormalization TuzaExpressionValues TuzaCertificate TuzaCertificateExpressions
variable {V : Type*} [DecidableEq V] [Fintype V]

theorem average_numerator (v : Point) (p q : ℝ) (hd : 1+p+q ≠ 0) :
    (1+p+q)*(cup v+averageValue v p q) =
      (1-v 5)*(1-2*v 5)/3+p*(v 0)*(v 0-v 5)+q*(v 1)*(v 1-v 5) := by
  dsimp [cup,averageValue]
  field_simp [hd]
  <;> ring

theorem conclusion_implies_tuza (S T : Finset V) (p q : ℕ) (hk : 43 ≤ Fintype.card V)
    (hs : 2 ≤ S.card) (ht : 2 ≤ T.card) (hst : S.card ≤ T.card)
    (htHalf : (Fintype.card V : ℝ)/2 ≤ T.card)
    (hp : p ≤ colorCount S.card) (hq : q ≤ colorCount T.card)
    (hcert : Conclusion (point (Fintype.card V) S.card T.card (S ∩ T).card p q)) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      2*packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by
  let k : ℝ := Fintype.card V
  let v := point k S.card T.card (S ∩ T).card p q
  let tau : ℝ := coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q))
  let nu : ℝ := 2*(packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ)
  have hkR : (43 : ℝ) ≤ k := by dsimp only [k]; exact_mod_cast hk
  have hk0 : 0 < k := by linarith
  have hp0 : 0 ≤ v 3 := by simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]; positivity
  have hq0 : 0 ≤ v 4 := by simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]; positivity
  have hpK : p ≤ Fintype.card V := hp.trans ((palette_bounds S.card hs).2.trans (card_le_univ S))
  have hqK : q ≤ Fintype.card V := hq.trans ((palette_bounds T.card ht).2.trans (card_le_univ T))
  have hp1 : v 3 ≤ 1 := by
    simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]
    apply (div_le_iff₀ hk0).mpr
    simpa only [one_mul] using (show (p : ℝ) ≤ k by dsimp only [k]; exact_mod_cast hpK)
  have hq1 : v 4 ≤ 1 := by
    simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]
    apply (div_le_iff₀ hk0).mpr
    simpa only [one_mul] using (show (q : ℝ) ≤ k by dsimp only [k]; exact_mod_cast hqK)
  have hr : 0 ≤ v 5 ∧ v 5 ≤ 1/34 := by
    simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]
    constructor
    · positivity
    · apply (div_le_iff₀ hk0).mpr
      linarith
  have hcover := cover_bounds S T p q (by omega) hst htHalf
  have hpacking := packing_bounds S T p q (by omega) hs ht hst hp hq
  change ∀ c ∈ coverValues v, tau/k^2 ≤ cup v+c at hcover
  change ∀ b ∈ packingValues v, cup v+b ≤ nu/k^2 at hpacking
  have hcommon : 0 ≤ (1+3*(v 3+v 4)^2)/16-
      (1+v 3+v 4)*(max 0 ((1+v 3+v 4)/2-v 2))^2 → tau/k^2 ≤ nu/k^2 := by
    intro hh
    have hc := hcover ((v 3)*(v 0-1/2)+(v 4)*(v 1-1/2)-(v 3+v 4)^2/4+
      (max 0 ((1+v 3+v 4)/2-v 2))^2) (by simp [coverValues,add_assoc])
    have hb := hpacking (averageValue v (v 3) (v 4)) (by simp [packingValues])
    have hd : 0 < 1+v 3+v 4 := by linarith
    have hn := average_numerator v (v 3) (v 4) hd.ne'
    have hmul := mul_le_mul_of_nonneg_left hb hd.le
    rw [hn] at hmul
    apply TuzaNormalizedScalar.common_criterion (v 0) (v 1) (v 3) (v 4) (v 5)
      (max 0 ((1+v 3+v 4)/2-v 2)) (tau/k^2) (nu/k^2) hp0 hq0 (by linarith) hr hh
    · dsimp [cup] at hc
      nlinarith only [hc]
    · exact hmul
  have h := conclusion_from_bounds v (tau/k^2) (nu/k^2) hcover hpacking hcommon hcert
  have hfinal : tau ≤ nu := (div_le_div_iff_of_pos_right (sq_pos_of_pos hk0)).mp h
  dsimp only [tau,nu] at hfinal
  exact_mod_cast hfinal

#print axioms average_numerator
#print axioms conclusion_implies_tuza
#check conclusion_implies_tuza
end TuzaNormalizedGraph

/-! Reduction of all graph parameters to the two checked certificates. -/
namespace TuzaFinalAssembly
open Finset TuzaCompression TuzaGraphCompression TuzaIndependentAllocation
  TuzaCoverCompression TuzaGraphTransfer TuzaGraphReductions TuzaRealBounds
  TuzaFiniteCertificate TuzaFiniteEnumeration TuzaCertificate TuzaCertificateExpressions
  TuzaNormalization TuzaNormalizedGraph
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- This is the domain of the continuous certificate, independent of any graph. -/
def ContinuousCertificate : Prop := ∀ v : Point, Domain v →
  (1/4 ≤ v 0 ∧ v 0 ≤ 1) → (1/2 ≤ v 1 ∧ v 1 ≤ 1) →
  (0 ≤ v 2 ∧ v 2 ≤ 1) → (0 ≤ v 3 ∧ v 3 ≤ 1) →
  (0 ≤ v 4 ∧ v 4 ≤ 1) → (0 ≤ v 5 ∧ v 5 ≤ 1/43) → Conclusion v

def FiniteCertificate (fallback : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Cut) : Prop :=
  ∀ k : ℕ, 2 ≤ k → k ≤ 42 → coreCheck fallback k = true

theorem replace_unused (S T U : Finset V) (p : ℕ) :
    packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin 0)) =
      packingNumber (twoAttached (⊤ : SimpleGraph V) S U (Fin p) (Fin 0)) ∧
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin 0)) =
      coverNumber (twoAttached (⊤ : SimpleGraph V) S U (Fin p) (Fin 0)) := by
  apply iso_parameters _ _ (Equiv.refl _)
  intro a b
  cases a with
  | inl a => cases b with
    | inl b => rfl
    | inr b => cases b with
      | inl b => rfl
      | inr b => exact Fin.elim0 b
  | inr a => cases a with
    | inl a => cases b with
      | inl b => rfl
      | inr b => rfl
    | inr a => exact Fin.elim0 a

theorem finite_ordered (fallback : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Cut)
    (hfinite : FiniteCertificate fallback) (S T : Finset V) (p q : ℕ)
    (hk : Fintype.card V ≤ 42) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card)
    (hst : S.card ≤ T.card) (hp : p ≤ colorCount S.card) (hq : q ≤ colorCount T.card) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      2*packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by
  have hsK := card_le_univ S
  have htK := card_le_univ T
  have hc := hfinite (Fintype.card V) (hs.trans hsK) hk
  by_cases hq0 : q = 0
  · subst q
    have he := replace_unused S T S p
    rw [he.1,he.2]
    apply witness_sound S S hs hs le_rfl p 0 hp (Nat.zero_le _)
    simpa only [inter_self] using one_type_checked fallback _ hc S.card p hs hsK hp
  · by_cases hp0 : p = 0
    · subst p
      have he := swap_types S T 0 q
      rw [he.1,he.2]
      have he' := replace_unused T S T q
      rw [he'.1,he'.2]
      apply witness_sound T T ht ht le_rfl q 0 hq (Nat.zero_le _)
      simpa only [inter_self] using one_type_checked fallback _ hc T.card q ht htK hq
    · have hu : S.card+T.card-Fintype.card V ≤ (S ∩ T).card ∧ (S ∩ T).card ≤ S.card := by
        have huK := card_le_univ (S ∪ T)
        have hid := card_union_add_card_inter S T
        exact ⟨by omega,card_le_card inter_subset_left⟩
      exact witness_sound S T hs ht hst p q hp hq _
        (two_type_checked fallback _ hc S.card T.card (S ∩ T).card p q hs hst htK hu
          ⟨by omega,hp⟩ ⟨by omega,hq⟩)

theorem continuous_ordered (hcontinuous : ContinuousCertificate)
    (S T : Finset V) (p q : ℕ) (hk : 43 ≤ Fintype.card V)
    (hs : 2 ≤ S.card) (ht : 2 ≤ T.card) (hst : S.card ≤ T.card)
    (hp : p ≤ colorCount S.card) (hq : q ≤ colorCount T.card) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      2*packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by
  by_cases hq0 : q = 0
  · subst q
    exact zero_second_type S T hs ht p hp hk
  by_cases hp0 : p = 0
  · subst p
    have he := swap_types S T 0 q
    rw [he.1,he.2]
    exact zero_second_type T S ht hs q hq hk
  by_cases hsSmall : (S.card : ℝ) ≤ (Fintype.card V : ℝ)/4
  · exact small_neighborhood S T hs ht p q hq hk hsSmall
  by_cases htSmall : (T.card : ℝ) ≤ (Fintype.card V : ℝ)/2
  · exact small_both_neighborhoods S T p q hk hst htSmall
  by_cases hmSmall : 3*(p+q) ≤ Fintype.card V+5
  · apply small_multiplicity S T p q hk (by linarith) ?_ hmSmall
    have hstR : (S.card : ℝ) ≤ T.card := by exact_mod_cast hst
    linarith
  let k : ℝ := Fintype.card V
  let v := point k S.card T.card (S ∩ T).card p q
  have hkR : (43 : ℝ) ≤ k := by dsimp only [k]; exact_mod_cast hk
  have hk0 : 0 < k := by linarith
  have div_le (a b : ℝ) (h : a ≤ b) : a/k ≤ b/k := (div_le_div_iff_of_pos_right hk0).mpr h
  have div_one (a : ℝ) (h : a ≤ k) : a/k ≤ 1 := (div_le_iff₀ hk0).mpr (by simpa only [one_mul] using h)
  have hpc : p ≤ S.card := hp.trans (palette_bounds S.card hs).2
  have hqc : q ≤ T.card := hq.trans (palette_bounds T.card ht).2
  have hsK : (S.card : ℝ) ≤ k := by dsimp only [k]; exact_mod_cast card_le_univ S
  have htK : (T.card : ℝ) ≤ k := by dsimp only [k]; exact_mod_cast card_le_univ T
  have huS : ((S ∩ T).card : ℝ) ≤ S.card := by exact_mod_cast card_le_card (inter_subset_left (s₁ := S) (s₂ := T))
  have hpS : (p : ℝ) ≤ S.card := by exact_mod_cast hpc
  have hqT : (q : ℝ) ≤ T.card := by exact_mod_cast hqc
  have hDom : Domain v := by
    constructor
    · exact div_le _ _ (by exact_mod_cast hst)
    · exact div_le _ _ huS
    · have hc := card_union_add_card_inter S T
      have huK := card_le_univ (S ∪ T)
      have hhR : (S.card : ℝ)+(T.card : ℝ) ≤ k+(S ∩ T).card := by dsimp only [k]; exact_mod_cast (show S.card+T.card ≤ Fintype.card V+(S ∩ T).card by omega)
      have hh : (S.card : ℝ)+(T.card : ℝ)-k ≤ (S ∩ T).card := by linarith only [hhR]
      have he : (S.card : ℝ)/k+(T.card : ℝ)/k-1 = ((S.card : ℝ)+(T.card : ℝ)-k)/k := by field_simp [hk0.ne'] <;> ring
      change (S.card : ℝ)/k+(T.card : ℝ)/k-1 ≤ ((S ∩ T).card : ℝ)/k
      rw [he]
      exact div_le _ _ hh
    · exact div_le _ _ hpS
    · exact div_le _ _ hqT
    · exact div_le _ _ (by exact_mod_cast (show 1 ≤ p by omega))
    · exact div_le _ _ (by exact_mod_cast (show 1 ≤ q by omega))
    · have hh : k+5 ≤ 3*((p : ℝ)+q) := by dsimp only [k]; exact_mod_cast (show Fintype.card V+5 ≤ 3*(p+q) by omega)
      have he1 : 1+5*(1/k) = (k+5)/k := by field_simp [hk0.ne'] <;> ring
      have he2 : 3*((p : ℝ)/k+(q : ℝ)/k) = (3*((p : ℝ)+q))/k := by ring
      change 1+5*(1/k) ≤ 3*((p : ℝ)/k+(q : ℝ)/k)
      rw [he1,he2]
      exact div_le _ _ hh
  have hx : 1/4 ≤ v 0 ∧ v 0 ≤ 1 := by
    constructor
    · apply (le_div_iff₀ hk0).mpr
      change (1/4)*k ≤ (S.card : ℝ)
      linarith
    · exact div_one _ hsK
  have hy : 1/2 ≤ v 1 ∧ v 1 ≤ 1 := by
    constructor
    · apply (le_div_iff₀ hk0).mpr
      change (1/2)*k ≤ (T.card : ℝ)
      linarith
    · exact div_one _ htK
  have hw : 0 ≤ v 2 ∧ v 2 ≤ 1 := ⟨by simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]; positivity,div_one _ (huS.trans hsK)⟩
  have hpv : 0 ≤ v 3 ∧ v 3 ≤ 1 := ⟨by simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]; positivity,div_one _ (hpS.trans hsK)⟩
  have hqv : 0 ≤ v 4 ∧ v 4 ≤ 1 := ⟨by simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]; positivity,div_one _ (hqT.trans htK)⟩
  have hr : 0 ≤ v 5 ∧ v 5 ≤ 1/43 := by
    constructor
    · simp only [v,point_0,point_1,point_2,point_3,point_4,point_5]; positivity
    · apply (div_le_iff₀ hk0).mpr
      linarith
  exact conclusion_implies_tuza S T p q hk hs ht hst (by linarith) hp hq
    (hcontinuous v hDom hx hy hw hpv hqv hr)

theorem active_model (fallback : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Cut)
    (hfinite : FiniteCertificate fallback) (hcontinuous : ContinuousCertificate)
    (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card) (p q : ℕ) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      2*packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by
  have hc := compress_both_types S T hs ht p q
  rw [hc.1,hc.2]
  have ordered (A B : Finset V) (ha : 2 ≤ A.card) (hb : 2 ≤ B.card) (hab : A.card ≤ B.card)
      (r z : ℕ) (hr : r ≤ colorCount A.card) (hz : z ≤ colorCount B.card) :
      coverNumber (twoAttached (⊤ : SimpleGraph V) A B (Fin r) (Fin z)) ≤
        2*packingNumber (twoAttached (⊤ : SimpleGraph V) A B (Fin r) (Fin z)) := by
    by_cases hk : Fintype.card V ≤ 42
    · exact finite_ordered fallback hfinite A B r z hk ha hb hab hr hz
    · exact continuous_ordered hcontinuous A B r z (by omega) ha hb hab hr hz
  by_cases hst : S.card ≤ T.card
  · exact ordered S T hs ht hst _ _ (min_le_right _ _) (min_le_right _ _)
  · have he := swap_types S T (min p (colorCount S.card)) (min q (colorCount T.card))
    rw [he.1,he.2]
    exact ordered T S ht hs (by omega) _ _ (min_le_right _ _) (min_le_right _ _)

#print axioms replace_unused
#print axioms finite_ordered
#print axioms continuous_ordered
#print axioms active_model
#check active_model
end TuzaFinalAssembly

/-! The public hypothesis counts distinct active neighborhoods, not vertices. -/
namespace TuzaFinalClassification
open Finset TuzaCompression TuzaGraphCompression TuzaCoverCompression
  TuzaIndependentAllocation TuzaGraphTransfer TuzaCoreCompletion TuzaRepresentation
  TuzaFiniteCertificate TuzaFinalAssembly TuzaCutCovers
variable {V C : Type*} [DecidableEq V] [DecidableEq C] [Fintype V] [Fintype C]

theorem small_core (N : C → Finset V) (hk : Fintype.card V < 2) :
    coverNumber (splitGraph N) ≤ 2*packingNumber (splitGraph N) := by
  have hzero : coverNumber (splitGraph N) ≤ 0 := by
    apply coverNumber_le_of_budget
    refine ⟨∅,⟨?_,?_⟩,by simp⟩
    · simp
    · intro t ht
      have hr : t.toRight.card ≤ 1 := by
        apply card_le_one.mpr
        intro a ha b hb
        by_contra hab
        have hh := ht.isClique (mem_toRight.mp ha) (mem_toRight.mp hb)
          (fun h => hab (Sum.inr.inj h))
        exact hh
      have hcard := card_toLeft_add_card_toRight (u := t)
      have htcard := ht.card_eq
      have hl := card_le_univ t.toLeft
      omega
  exact hzero.trans (Nat.zero_le _)

theorem cover_two {A : Type*} [DecidableEq A] [Inhabited A] (F : Finset A) (hc : F.card ≤ 2) :
    ∃ a b : A, ∀ x ∈ F, x = a ∨ x = b := by
  by_cases hnon : F.Nonempty
  · obtain ⟨a,ha⟩ := hnon
    by_cases hsecond : (F.erase a).Nonempty
    · obtain ⟨b,hb⟩ := hsecond
      have hba := (mem_erase.mp hb).1
      have hbF := (mem_erase.mp hb).2
      refine ⟨a,b,?_⟩
      intro x hx
      by_cases hxa : x = a
      · exact Or.inl hxa
      by_cases hxb : x = b
      · exact Or.inr hxb
      have hsub : ({a,b,x} : Finset A) ⊆ F := by
        intro y hy
        simp only [mem_insert,mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact ha
        · exact hbF
        · exact hx
      have hthree : ({a,b,x} : Finset A).card = 3 := by
        simp [hxa,hxb,hba,Ne.symm hxa,Ne.symm hxb,Ne.symm hba]
      have hh := card_le_card hsub
      omega
    · refine ⟨a,a,?_⟩
      intro x hx
      by_cases hxa : x = a
      · exact Or.inl hxa
      · exact False.elim (hsecond ⟨x,mem_erase.mpr ⟨hxa,hx⟩⟩)
  · exact ⟨default,default,fun x hx => False.elim (hnon ⟨x,hx⟩)⟩

noncomputable def activeTypes (G : SimpleGraph V) (K : Finset V) : Finset (Finset {v // v ∈ K}) := by
  classical
  exact (univ.image (neighbors G K)).filter (fun S => 2 ≤ S.card)

/-- Conditional assembly: the final module supplies both kernel-checked certificates. -/
theorem split_graph_two_active_types
    (fallback : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Cut)
    (hfinite : FiniteCertificate fallback) (hcontinuous : ContinuousCertificate)
    (G : SimpleGraph V) (K : Finset V) (hK : G.IsClique K)
    (hI : ∀ a ∉ K, ∀ b ∉ K, ¬G.Adj a b) (htypes : (activeTypes G K).card ≤ 2) :
    coverNumber G ≤ 2*packingNumber G := by
  classical
  by_cases hk : Fintype.card {v // v ∈ K} < 2
  · have he := iso_parameters (splitGraph (neighbors G K)) G (partitionEquiv K)
      (partition_adjacency G K hK hI)
    rw [← he.1,← he.2]
    exact small_core (neighbors G K) hk
  have hk2 : 2 ≤ Fintype.card {v // v ∈ K} := by omega
  obtain ⟨S,T,hST⟩ := cover_two (activeTypes G K) htypes
  let S' : Finset {v // v ∈ K} := if 2 ≤ S.card then S else univ
  let T' : Finset {v // v ∈ K} := if 2 ≤ T.card then T else univ
  have hs : 2 ≤ S'.card := by dsimp [S']; split_ifs <;> simp_all
  have ht : 2 ≤ T'.card := by dsimp [T']; split_ifs <;> simp_all
  apply split_from_fin G K hK hI S' T' ?_ ?_
  · intro c hc
    have hmem : neighbors G K c ∈ activeTypes G K := by
      simp only [activeTypes,mem_filter,mem_image,mem_univ,true_and]
      exact ⟨⟨c,rfl⟩,hc⟩
    rcases hST _ hmem with h | h
    · left
      have hh : 2 ≤ S.card := by rwa [h] at hc
      simpa only [S',if_pos hh] using h
    · right
      have hh : 2 ≤ T.card := by rwa [h] at hc
      simpa only [T',if_pos hh] using h
  · intro p q
    exact active_model fallback hfinite hcontinuous S' T' hs ht p q

#print axioms small_core
#print axioms cover_two
#print axioms split_graph_two_active_types
#check split_graph_two_active_types
end TuzaFinalClassification
