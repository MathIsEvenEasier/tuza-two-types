import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Max
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Tauto

/-!
Complete-graph edge colorings and the packing recoloring construction.
Vertices and triangles are finite sets; edge-disjointness refers to their
actual two-element subsets. OpenAI Codex (GPT-6 Astra), 2026-10-07.
-/

open Finset
namespace TuzaCompression

structure PairColoring (V C : Type*) where
  color : V → V → C
  symm : ∀ a b, color a b = color b a
  proper : ∀ a b c, a ≠ b → a ≠ c → color a b = color a c → b = c

variable {V C : Type*}

def sumColoring (G : Type*) [AddCommGroup G] : PairColoring G G where
  color a b := a + b
  symm := add_comm
  proper _ _ _ _ _ h := add_left_cancel h

def optionColor {G : Type*} [AddCommGroup G] : Option G → Option G → G
  | none, none => 0
  | none, some b => b + b
  | some a, none => a + a
  | some a, some b => a + b

def optionColoring (G : Type*) [AddCommGroup G]
    (hdouble : Function.Injective (fun a : G => a + a)) : PairColoring (Option G) G where
  color := optionColor
  symm a b := by cases a <;> cases b <;> simp [optionColor, add_comm]
  proper a b c hab hac h := by
    cases a with
    | none =>
      cases b with
      | none => exact False.elim (hab rfl)
      | some b =>
        cases c with
        | none => exact False.elim (hac rfl)
        | some c => exact congrArg some (hdouble h)
    | some a =>
      cases b with
      | none =>
        cases c with
        | none => rfl
        | some c =>
          have hh : a = c := add_left_cancel h
          exact False.elim (hac (congrArg some hh))
      | some b =>
        cases c with
        | none =>
          have hh : b = a := add_left_cancel h
          exact False.elim (hab (congrArg some hh.symm))
        | some c => exact congrArg some (add_left_cancel h)

theorem double_injective (n : ℕ) (hodd : n % 2 = 1) :
    Function.Injective (fun a : ZMod n => a + a) := by
  have hu : IsUnit (2 : ZMod n) := by
    apply ZMod.isUnit_prime_of_not_dvd Nat.prime_two
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    omega
  have hi := ZMod.inv_mul_of_unit (2 : ZMod n) hu
  intro a b h
  have hh := congrArg (fun x => (2 : ZMod n)⁻¹ * x) h
  simpa only [← two_mul, ← mul_assoc, hi, one_mul] using hh

def colorCount (s : ℕ) : ℕ := if s % 2 = 0 then s - 1 else s

def PairColoring.transport {W D : Type*} (f : PairColoring W D)
    (ev : V ≃ W) (ec : D ≃ C) : PairColoring V C where
  color a b := ec (f.color (ev a) (ev b))
  symm a b := congrArg ec (f.symm _ _)
  proper a b c hab hac hh := ev.injective
    (f.proper _ _ _ (fun h => hab (ev.injective h))
      (fun h => hac (ev.injective h)) (ec.injective hh))

/-- The sharp number of available colors, uniformly for every finite size >= 2. -/
theorem complete_graph_coloring [Fintype V] (hs : 2 ≤ Fintype.card V) :
    Nonempty (PairColoring V (Fin (colorCount (Fintype.card V)))) := by
  classical
  let n := Fintype.card V
  by_cases he : n % 2 = 0
  · have hn : n - 1 ≠ 0 := by omega
    letI : NeZero (n - 1) := ⟨hn⟩
    have ho : (n - 1) % 2 = 1 := by omega
    let ev : V ≃ Option (ZMod (n - 1)) := Fintype.equivOfCardEq (by simp; omega)
    let ec : ZMod (n - 1) ≃ Fin (colorCount n) :=
      Fintype.equivOfCardEq (by simp [colorCount, he])
    exact ⟨(optionColoring _ (double_injective _ ho)).transport ev ec⟩
  · have hn : n ≠ 0 := by omega
    letI : NeZero n := ⟨hn⟩
    let ev : V ≃ ZMod n := Fintype.equivOfCardEq (by simp [n])
    let ec : ZMod n ≃ Fin (colorCount n) :=
      Fintype.equivOfCardEq (by simp [colorCount, he])
    exact ⟨(sumColoring _).transport ev ec⟩

variable [DecidableEq V]

/-- A two-element set has a well-defined color, independent of endpoint order. -/
theorem PairColoring.edge_color_exists (f : PairColoring V C) [Nonempty C]
    (e : Finset V) : ∃ c : C, ∀ a b, a ≠ b → e = {a, b} → c = f.color a b := by
  classical
  by_cases he : e.card = 2
  · obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp he
    refine ⟨f.color x y, ?_⟩
    intro a b hab habset
    have hx : x = a ∨ x = b := by
      have : x ∈ ({a, b} : Finset V) := habset ▸ (by simp)
      simpa using this
    have hy : y = a ∨ y = b := by
      have : y ∈ ({a, b} : Finset V) := habset ▸ (by simp)
      simpa using this
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (hxy rfl)
    · rfl
    · exact f.symm _ _
    · exact False.elim (hxy rfl)
  · obtain ⟨c⟩ := ‹Nonempty C›
    refine ⟨c, ?_⟩
    intro a b hab heq
    exact False.elim (he (heq ▸ card_pair hab))

noncomputable def PairColoring.edgeColor (f : PairColoring V C) [Nonempty C]
    (e : Finset V) : C := Classical.choose (f.edge_color_exists e)

theorem PairColoring.edgeColor_pair (f : PairColoring V C) [Nonempty C]
    {a b : V} (hab : a ≠ b) : f.edgeColor {a, b} = f.color a b :=
  Classical.choose_spec (f.edge_color_exists {a, b}) a b hab rfl

/-- Equal-colored edges meeting at a vertex must be the same edge. -/
theorem PairColoring.edgeColor_proper (f : PairColoring V C) [Nonempty C]
    {e d : Finset V} (he : e.card = 2) (hd : d.card = 2)
    {v : V} (hve : v ∈ e) (hvd : v ∈ d)
    (hc : f.edgeColor e = f.edgeColor d) : e = d := by
  have repr : ∀ t : Finset V, t.card = 2 → v ∈ t → ∃ b, v ≠ b ∧ t = {v, b} := by
    intro t ht hv
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp ht
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact ⟨b, hab, rfl⟩
    · exact ⟨a, hab.symm, pair_comm _ _⟩
  obtain ⟨a, ha, rfl⟩ := repr e he hve
  obtain ⟨b, hb, rfl⟩ := repr d hd hvd
  rw [f.edgeColor_pair ha, f.edgeColor_pair hb] at hc
  rw [f.proper v a b ha hb hc]

variable [DecidableEq C]

def lift (t : Finset V) : Finset (V ⊕ C) := t.image Sum.inl

def cone (color : Finset V → C) (e : Finset V) : Finset (V ⊕ C) :=
  insert (Sum.inr (color e)) (lift e)

@[simp] theorem inl_mem_lift {v : V} {t : Finset V} :
    Sum.inl v ∈ lift (C := C) t ↔ v ∈ t := by simp [lift]
@[simp] theorem inr_not_mem_lift {c : C} {t : Finset V} :
    Sum.inr c ∉ lift t := by simp [lift]
@[simp] theorem inl_mem_cone {color : Finset V → C} {v : V} {e : Finset V} :
    Sum.inl v ∈ cone color e ↔ v ∈ e := by simp [cone]
@[simp] theorem inr_mem_cone {color : Finset V → C} {c : C} {e : Finset V} :
    Sum.inr c ∈ cone color e ↔ c = color e := by simp [cone]

theorem lift_injective : Function.Injective (lift (V := V) (C := C)) := by
  intro t u h
  ext v
  have hh := congrArg (fun s => Sum.inl v ∈ s) h
  simpa using hh

theorem cone_injective (color : Finset V → C) : Function.Injective (cone color) := by
  intro e d h
  ext v
  have hh := congrArg (fun s => Sum.inl v ∈ s) h
  simpa using hh

@[simp] theorem lift_card (t : Finset V) : (lift (C := C) t).card = t.card := by
  exact card_image_of_injective t Sum.inl_injective

theorem cone_card (color : Finset V → C) (e : Finset V) :
    (cone color e).card = e.card + 1 := by simp [cone]

theorem edge_subset_eq {a b : V} {e : Finset V}
    (hab : a ≠ b) (he : e.card = 2) (ha : a ∈ e) (hb : b ∈ e) :
    ({a, b} : Finset V) = e := by
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [he, card_pair hab]

/-- Recoloring core edges gives actual edge-disjoint triangles. -/
theorem cones_edge_disjoint (J : Finset (Finset V))
    (hJ : ∀ e ∈ J, e.card = 2) (color : Finset V → C)
    (proper : ∀ e ∈ J, ∀ d ∈ J, ∀ v ∈ e, v ∈ d → color e = color d → e = d) :
    ((J.image (cone color)) : Set (Finset (V ⊕ C))).PairwiseDisjoint
      (fun t => t.powersetCard 2) := by
  intro t ht u hu hne
  obtain ⟨e, he, rfl⟩ := mem_image.mp ht
  obtain ⟨d, hd, rfl⟩ := mem_image.mp hu
  apply disjoint_left.mpr
  intro q hqt hqu
  obtain ⟨hqe, hq⟩ := mem_powersetCard.mp hqt
  obtain ⟨hqd, _⟩ := mem_powersetCard.mp hqu
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hq
  have hae := hqe (by simp : a ∈ ({a, b} : Finset (V ⊕ C)))
  have hbe := hqe (by simp : b ∈ ({a, b} : Finset (V ⊕ C)))
  have had := hqd (by simp : a ∈ ({a, b} : Finset (V ⊕ C)))
  have hbd := hqd (by simp : b ∈ ({a, b} : Finset (V ⊕ C)))
  apply hne
  apply congrArg (cone color)
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hab' : a ≠ b := fun h => hab (congrArg Sum.inl h)
      exact (edge_subset_eq hab' (hJ e he) (by simpa using hae) (by simpa using hbe)).symm.trans
        (edge_subset_eq hab' (hJ d hd) (by simpa using had) (by simpa using hbd))
    | inr b =>
      exact proper e he d hd a (by simpa using hae) (by simpa using had)
        ((inr_mem_cone.mp hbe).symm.trans (inr_mem_cone.mp hbd))
  | inr a =>
    cases b with
    | inl b =>
      exact proper e he d hd b (by simpa using hbe) (by simpa using hbd)
        ((inr_mem_cone.mp hae).symm.trans (inr_mem_cone.mp had))
    | inr b =>
      exact False.elim (hab (congrArg Sum.inr
        ((inr_mem_cone.mp hae).trans (inr_mem_cone.mp hbe).symm)))

/-- Any selected core edges can be packed on exactly h(s) available centers.
The conclusion concerns finite sets of vertices and their two-element edges. -/
theorem centered_packing [Fintype V] (hs : 2 ≤ Fintype.card V)
    (J : Finset (Finset V)) (hJ : ∀ e ∈ J, e.card = 2) :
    ∃ P : Finset (Finset (V ⊕ Fin (colorCount (Fintype.card V)))),
      P.card = J.card ∧
      (∀ t ∈ P, t.card = 3) ∧
      (P : Set (Finset (V ⊕ Fin (colorCount (Fintype.card V))))).PairwiseDisjoint
        (fun t => t.powersetCard 2) ∧
      (∀ e ∈ J, ∃ c, insert (Sum.inr c) (lift e) ∈ P) := by
  classical
  have hh : 0 < colorCount (Fintype.card V) := by unfold colorCount; split <;> omega
  letI : NeZero (colorCount (Fintype.card V)) := ⟨by omega⟩
  obtain ⟨f⟩ := complete_graph_coloring (V := V) hs
  refine ⟨J.image (cone f.edgeColor), card_image_of_injective J (cone_injective _), ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨e, he, rfl⟩ := mem_image.mp ht
    rw [cone_card, hJ e he]
  · exact cones_edge_disjoint J hJ f.edgeColor (fun e he d hd v hve hvd hc =>
      f.edgeColor_proper (hJ e he) (hJ d hd) hve hvd hc)
  · intro e he
    exact ⟨f.edgeColor e, mem_image.mpr ⟨e, he, rfl⟩⟩

#print axioms complete_graph_coloring
#print axioms centered_packing
#check centered_packing

/-- Lifting old vertices into the left summand preserves their edge-disjointness. -/
theorem lift_packing (Q : Finset (Finset V))
    (hQ : (Q : Set (Finset V)).PairwiseDisjoint (fun t => t.powersetCard 2)) :
    ((Q.image (lift (C := C))) : Set (Finset (V ⊕ C))).PairwiseDisjoint
      (fun t => t.powersetCard 2) := by
  intro t ht u hu hne
  obtain ⟨t0, ht0, rfl⟩ := mem_image.mp ht
  obtain ⟨u0, hu0, rfl⟩ := mem_image.mp hu
  have hne' : t0 ≠ u0 := fun h => hne (congrArg lift h)
  apply disjoint_left.mpr
  intro q hqt hqu
  obtain ⟨hqt', hq⟩ := mem_powersetCard.mp hqt
  obtain ⟨hqu', _⟩ := mem_powersetCard.mp hqu
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hq
  have hat := hqt' (by simp : a ∈ ({a, b} : Finset (V ⊕ C)))
  have hbt := hqt' (by simp : b ∈ ({a, b} : Finset (V ⊕ C)))
  have hau := hqu' (by simp : a ∈ ({a, b} : Finset (V ⊕ C)))
  have hbu := hqu' (by simp : b ∈ ({a, b} : Finset (V ⊕ C)))
  cases a with
  | inr a => exact inr_not_mem_lift hat
  | inl a =>
    cases b with
    | inr b => exact inr_not_mem_lift hbt
    | inl b =>
      have hab' : a ≠ b := fun h => hab (congrArg Sum.inl h)
      apply disjoint_left.mp (hQ ht0 hu0 hne')
      · exact mem_powersetCard.mpr ⟨by
          intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact inl_mem_lift.mp hat
          · exact inl_mem_lift.mp hbt, card_pair hab'⟩
      · exact mem_powersetCard.mpr ⟨by
          intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact inl_mem_lift.mp hau
          · exact inl_mem_lift.mp hbu, card_pair hab'⟩

/-- An old triangle and a recolored triangle can collide only on the retained core edge. -/
theorem cone_lift_disjoint (color : Finset V → C) {e t : Finset V}
    (he : e.card = 2) (havoid : ¬ e ⊆ t) :
    Disjoint ((cone color e).powersetCard 2) ((lift t).powersetCard 2) := by
  apply disjoint_left.mpr
  intro q hqc hql
  obtain ⟨hqc', hq⟩ := mem_powersetCard.mp hqc
  obtain ⟨hql', _⟩ := mem_powersetCard.mp hql
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hq
  have hae := hqc' (by simp : a ∈ ({a, b} : Finset (V ⊕ C)))
  have hbe := hqc' (by simp : b ∈ ({a, b} : Finset (V ⊕ C)))
  have hat := hql' (by simp : a ∈ ({a, b} : Finset (V ⊕ C)))
  have hbt := hql' (by simp : b ∈ ({a, b} : Finset (V ⊕ C)))
  cases a with
  | inr a => exact inr_not_mem_lift hat
  | inl a =>
    cases b with
    | inr b => exact inr_not_mem_lift hbt
    | inl b =>
      have hab' : a ≠ b := fun h => hab (congrArg Sum.inl h)
      have heq := edge_subset_eq hab' he (inl_mem_cone.mp hae) (inl_mem_cone.mp hbe)
      apply havoid
      rw [← heq]
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact inl_mem_lift.mp hat
      · exact inl_mem_lift.mp hbt

/-- The complete recoloring step: keep every old triangle, add one triangle
for each selected core edge, and preserve both cardinality and disjointness. -/
theorem preserve_old_packing (Q J : Finset (Finset V))
    (hQcard : ∀ t ∈ Q, t.card = 3)
    (hQ : (Q : Set (Finset V)).PairwiseDisjoint (fun t => t.powersetCard 2))
    (hJ : ∀ e ∈ J, e.card = 2)
    (havoid : ∀ e ∈ J, ∀ t ∈ Q, ¬ e ⊆ t)
    (color : Finset V → C)
    (proper : ∀ e ∈ J, ∀ d ∈ J, ∀ v ∈ e, v ∈ d → color e = color d → e = d) :
    ∃ P : Finset (Finset (V ⊕ C)),
      P.card = Q.card + J.card ∧
      (∀ t ∈ P, t.card = 3) ∧
      (P : Set (Finset (V ⊕ C))).PairwiseDisjoint (fun t => t.powersetCard 2) ∧
      (∀ t ∈ Q, lift t ∈ P) ∧ (∀ e ∈ J, cone color e ∈ P) := by
  let A := Q.image (lift (C := C))
  let B := J.image (cone color)
  have hab : Disjoint A B := by
    apply disjoint_left.mpr
    intro t ht hu
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
    obtain ⟨e, he, heq⟩ := mem_image.mp hu
    have hc : Sum.inr (color e) ∈ cone color e := by simp
    rw [heq] at hc
    exact inr_not_mem_lift hc
  refine ⟨A ∪ B, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_union_of_disjoint hab]
    change (Q.image (lift (C := C))).card + (J.image (cone color)).card = _
    rw [card_image_of_injective Q lift_injective,
      card_image_of_injective J (cone_injective color)]
  · intro t ht
    rcases mem_union.mp ht with ht | ht
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
      simpa using hQcard q hq
    · obtain ⟨e, he, rfl⟩ := mem_image.mp ht
      rw [cone_card, hJ e he]
  · intro t ht u hu hne
    rcases mem_union.mp ht with ht | ht <;> rcases mem_union.mp hu with hu | hu
    · exact lift_packing Q hQ ht hu hne
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
      obtain ⟨e, he, rfl⟩ := mem_image.mp hu
      exact (cone_lift_disjoint color (hJ e he) (havoid e he q hq)).symm
    · obtain ⟨e, he, rfl⟩ := mem_image.mp ht
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hu
      exact cone_lift_disjoint color (hJ e he) (havoid e he q hq)
    · exact cones_edge_disjoint J hJ color proper ht hu hne
  · intro t ht
    exact mem_union_left _ (mem_image.mpr ⟨t, ht, rfl⟩)
  · intro e he
    exact mem_union_right _ (mem_image.mpr ⟨e, he, rfl⟩)

#print axioms preserve_old_packing

/-- Recolor inside a specified neighborhood of an otherwise arbitrary old vertex set.
The number of new centers depends on |S|, not on the size of the old graph. -/
theorem recolor_on_neighborhood (S : Finset V) (hs : 2 ≤ S.card)
    (Q J : Finset (Finset V))
    (hQcard : ∀ t ∈ Q, t.card = 3)
    (hQ : (Q : Set (Finset V)).PairwiseDisjoint (fun t => t.powersetCard 2))
    (hJ : ∀ e ∈ J, e.card = 2)
    (hJS : ∀ e ∈ J, e ⊆ S)
    (havoid : ∀ e ∈ J, ∀ t ∈ Q, ¬ e ⊆ t) :
    ∃ P : Finset (Finset (V ⊕ Fin (colorCount S.card))),
      P.card = Q.card + J.card ∧
      (∀ t ∈ P, t.card = 3) ∧
      (P : Set (Finset (V ⊕ Fin (colorCount S.card)))).PairwiseDisjoint
        (fun t => t.powersetCard 2) ∧
      (∀ t ∈ Q, lift t ∈ P) ∧
      (∀ e ∈ J, ∃ c, insert (Sum.inr c) (lift e) ∈ P) := by
  classical
  obtain ⟨w, hw⟩ := card_pos.mp (show 0 < S.card by omega)
  let r : V → S := fun v => if hv : v ∈ S then ⟨v, hv⟩ else ⟨w, hw⟩
  have hr : ∀ v ∈ S, (r v).val = v := by
    intro v hv
    simp [r, hv]
  have hrcard : ∀ e ∈ J, (e.image r).card = 2 := by
    intro e he
    rw [card_image_of_injOn, hJ e he]
    intro a ha b hb hh
    have hh' := congrArg Subtype.val hh
    simpa only [hr a (hJS e he ha), hr b (hJS e he hb)] using hh'
  have hrecover : ∀ e ∈ J, (e.image r).image Subtype.val = e := by
    intro e he
    ext v
    simp only [mem_image]
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, hab⟩
      have : b = v := (hr b (hJS e he hb)).symm.trans hab
      simpa [this] using hb
    · intro hv
      exact ⟨r v, ⟨v, hv, rfl⟩, hr v (hJS e he hv)⟩
  have hs' : 2 ≤ Fintype.card S := by simpa using hs
  have hcpos : 0 < colorCount (Fintype.card S) := by
    unfold colorCount
    split <;> omega
  letI : NeZero (colorCount (Fintype.card S)) := ⟨by omega⟩
  obtain ⟨f⟩ := complete_graph_coloring (V := S) hs'
  let color : Finset V → Fin (colorCount S.card) := fun e =>
    Fin.cast (by simp) (f.edgeColor (e.image r))
  have proper : ∀ e ∈ J, ∀ d ∈ J, ∀ v ∈ e, v ∈ d → color e = color d → e = d := by
    intro e he d hd v hve hvd hcol
    have hc : f.edgeColor (e.image r) = f.edgeColor (d.image r) := by
      have hh := congrArg Fin.val hcol
      exact Fin.ext hh
    have hmap := f.edgeColor_proper (hrcard e he) (hrcard d hd)
      (mem_image.mpr ⟨v, hve, rfl⟩) (mem_image.mpr ⟨v, hvd, rfl⟩) hc
    have hh := congrArg (fun t => t.image Subtype.val) hmap
    simpa only [hrecover e he, hrecover d hd] using hh
  obtain ⟨P, hcard, htri, hdis, hkeep, hcones⟩ :=
    preserve_old_packing Q J hQcard hQ hJ havoid color proper
  refine ⟨P, hcard, htri, hdis, hkeep, ?_⟩
  intro e he
  exact ⟨color e, hcones e he⟩

#print axioms recolor_on_neighborhood
#check recolor_on_neighborhood

end TuzaCompression

/-!
Exact packing multiplicity compression for arbitrary simple graphs.
The preceding construction is included verbatim from the verified module.
No assumption that the common neighborhood is a clique is needed here.
-/
namespace TuzaGraphCompression
open TuzaCompression Finset

variable {V C D W : Type*} [DecidableEq V] [DecidableEq C] [DecidableEq D]

def attached (H : SimpleGraph V) (S : Finset V) (C : Type*) : SimpleGraph (V ⊕ C) where
  Adj a b := match a, b with
    | .inl x, .inl y => H.Adj x y
    | .inl x, .inr _ => x ∈ S
    | .inr _, .inl y => y ∈ S
    | .inr _, .inr _ => False
  symm.symm a b h := by
    cases a <;> cases b
    · exact H.adj_symm h
    · exact h
    · exact h
    · exact h
  loopless.irrefl a := by
    cases a with
    | inl a => exact H.irrefl
    | inr a => exact id

def IsPacking (H : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ t ∈ P, H.IsNClique 3 t) ∧
    (P : Set (Finset V)).PairwiseDisjoint (fun t => t.powersetCard 2)

theorem right_card_le_one {H : SimpleGraph V} {S : Finset V} {t : Finset (V ⊕ C)}
    (ht : (attached H S C).IsNClique 3 t) : t.toRight.card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha b hb
  by_contra hne
  have hf := ht.isClique (mem_toRight.mp ha) (mem_toRight.mp hb)
    (fun h => hne (Sum.inr.inj h))
  exact hf

theorem left_isClique {H : SimpleGraph V} {S : Finset V} {t : Finset (V ⊕ C)}
    (ht : (attached H S C).IsNClique 3 t) : H.IsClique t.toLeft := by
  intro a ha b hb hne
  exact ht.isClique (mem_toLeft.mp ha) (mem_toLeft.mp hb)
    (fun h => hne (Sum.inl.inj h))

theorem left_card_ge_two {H : SimpleGraph V} {S : Finset V} {t : Finset (V ⊕ C)}
    (ht : (attached H S C).IsNClique 3 t) : 2 ≤ t.toLeft.card := by
  have hh := card_toLeft_add_card_toRight (u := t)
  have hr := right_card_le_one ht
  have hc := ht.card_eq
  omega

theorem left_card_old {H : SimpleGraph V} {S : Finset V} {t : Finset (V ⊕ C)}
    (ht : (attached H S C).IsNClique 3 t) (hr : t.toRight = ∅) : t.toLeft.card = 3 := by
  have hh := card_toLeft_add_card_toRight (u := t)
  simpa [hr, ht.card_eq] using hh

theorem left_card_new {H : SimpleGraph V} {S : Finset V} {t : Finset (V ⊕ C)}
    (ht : (attached H S C).IsNClique 3 t) (hr : t.toRight ≠ ∅) : t.toLeft.card = 2 := by
  have hh := card_toLeft_add_card_toRight (u := t)
  have hle := right_card_le_one ht
  have hp : 0 < t.toRight.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hr)
  have hc := ht.card_eq
  omega

theorem left_subset_neighborhood {H : SimpleGraph V} {S : Finset V}
    {t : Finset (V ⊕ C)} (ht : (attached H S C).IsNClique 3 t)
    (hr : t.toRight ≠ ∅) : t.toLeft ⊆ S := by
  obtain ⟨c, hc⟩ := nonempty_iff_ne_empty.mpr hr
  intro v hv
  exact ht.isClique (mem_toLeft.mp hv) (mem_toRight.mp hc) (by simp)

theorem lift_subset_of_left {e : Finset V} {t : Finset (V ⊕ C)}
    (he : e ⊆ t.toLeft) : lift e ⊆ t := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
  exact mem_toLeft.mp (he hv)

/-- Any shared two-element subset of the old vertices forces equality. -/
theorem core_collision {H : SimpleGraph V} {S : Finset V}
    {P : Finset (Finset (V ⊕ C))} (hP : IsPacking (attached H S C) P)
    {t u : Finset (V ⊕ C)} (ht : t ∈ P) (hu : u ∈ P)
    {e : Finset V} (he : e.card = 2) (het : e ⊆ t.toLeft) (heu : e ⊆ u.toLeft) : t = u := by
  by_contra hne
  have hec : (lift (C := C) e).card = 2 := by simpa using he
  exact disjoint_left.mp (hP.2 ht hu hne)
    (mem_powersetCard.mpr ⟨lift_subset_of_left het, hec⟩)
    (mem_powersetCard.mpr ⟨lift_subset_of_left heu, hec⟩)

theorem core_injective {H : SimpleGraph V} {S : Finset V}
    {P : Finset (Finset (V ⊕ C))} (hP : IsPacking (attached H S C) P) :
    Set.InjOn Finset.toLeft (P : Set (Finset (V ⊕ C))) := by
  intro t ht u hu htu
  obtain ⟨e, het, he⟩ := exists_subset_card_eq (left_card_ge_two (hP.1 t ht))
  exact core_collision hP ht hu he het (htu ▸ het)

/-- Extract the hypotheses required by the recoloring construction from any graph packing. -/
theorem extract_packing {H : SimpleGraph V} {S : Finset V}
    {P : Finset (Finset (V ⊕ C))} (hP : IsPacking (attached H S C) P) :
    ∃ Q J : Finset (Finset V),
      IsPacking H Q ∧
      (∀ e ∈ J, H.IsNClique 2 e) ∧
      (∀ e ∈ J, e ⊆ S) ∧
      (∀ e ∈ J, ∀ q ∈ Q, ¬ e ⊆ q) ∧ P.card = Q.card + J.card := by
  classical
  let A := P.filter (fun t => t.toRight = ∅)
  let B := P.filter (fun t => ¬ t.toRight = ∅)
  let Q := A.image Finset.toLeft
  let J := B.image Finset.toLeft
  have hQ : IsPacking H Q := by
    constructor
    · intro q hq
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
      have htP := (mem_filter.mp ht).1
      exact ⟨left_isClique (hP.1 t htP), left_card_old (hP.1 t htP) (mem_filter.mp ht).2⟩
    · intro q hq r hr hne
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hr
      apply disjoint_left.mpr
      intro e het heu
      obtain ⟨het', he⟩ := mem_powersetCard.mp het
      obtain ⟨heu', _⟩ := mem_powersetCard.mp heu
      exact hne (congrArg Finset.toLeft (core_collision hP
        (mem_filter.mp ht).1 (mem_filter.mp hu).1 he het' heu'))
  refine ⟨Q, J, hQ, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨t, ht, rfl⟩ := mem_image.mp he
    have htP := (mem_filter.mp ht).1
    exact ⟨left_isClique (hP.1 t htP), left_card_new (hP.1 t htP) (mem_filter.mp ht).2⟩
  · intro e he
    obtain ⟨t, ht, rfl⟩ := mem_image.mp he
    exact left_subset_neighborhood (hP.1 t (mem_filter.mp ht).1) (mem_filter.mp ht).2
  · intro e he q hq hesub
    obtain ⟨t, ht, rfl⟩ := mem_image.mp he
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hq
    have htu := core_collision hP (mem_filter.mp ht).1 (mem_filter.mp hu).1
      (left_card_new (hP.1 t (mem_filter.mp ht).1) (mem_filter.mp ht).2) (Subset.refl _) hesub
    apply (mem_filter.mp ht).2
    rw [htu]
    exact (mem_filter.mp hu).2
  · have hA : Q.card = A.card := card_image_of_injOn (fun t ht u hu h =>
        core_injective hP (mem_filter.mp ht).1 (mem_filter.mp hu).1 h)
    have hB : J.card = B.card := card_image_of_injOn (fun t ht u hu h =>
        core_injective hP (mem_filter.mp ht).1 (mem_filter.mp hu).1 h)
    rw [hA, hB]
    exact (card_filter_add_card_filter_not (s := P) (fun t => t.toRight = ∅)).symm

/-- A proper coloring of the selected edges inside S, in ambient V. -/
theorem neighborhood_coloring (S : Finset V) (hs : 2 ≤ S.card)
    (J : Finset (Finset V)) (hJ : ∀ e ∈ J, e.card = 2) (hJS : ∀ e ∈ J, e ⊆ S) :
    ∃ color : Finset V → Fin (colorCount S.card),
      ∀ e ∈ J, ∀ d ∈ J, ∀ v ∈ e, v ∈ d → color e = color d → e = d := by
  classical
  obtain ⟨w, hw⟩ := card_pos.mp (show 0 < S.card by omega)
  let r : V → S := fun v => if hv : v ∈ S then ⟨v, hv⟩ else ⟨w, hw⟩
  have hr : ∀ v ∈ S, (r v).val = v := by intro v hv; simp [r, hv]
  have hrcard : ∀ e ∈ J, (e.image r).card = 2 := by
    intro e he
    rw [card_image_of_injOn, hJ e he]
    intro a ha b hb hh
    have hh' := congrArg Subtype.val hh
    simpa only [hr a (hJS e he ha), hr b (hJS e he hb)] using hh'
  have hrecover : ∀ e ∈ J, (e.image r).image Subtype.val = e := by
    intro e he
    ext v
    simp only [mem_image]
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, hab⟩
      have : b = v := (hr b (hJS e he hb)).symm.trans hab
      simpa [this] using hb
    · intro hv
      exact ⟨r v, ⟨v, hv, rfl⟩, hr v (hJS e he hv)⟩
  have hs' : 2 ≤ Fintype.card S := by simpa using hs
  have hcpos : 0 < colorCount (Fintype.card S) := by unfold colorCount; split <;> omega
  letI : NeZero (colorCount (Fintype.card S)) := ⟨by omega⟩
  obtain ⟨f⟩ := complete_graph_coloring (V := S) hs'
  let color : Finset V → Fin (colorCount S.card) := fun e =>
    Fin.cast (by simp) (f.edgeColor (e.image r))
  refine ⟨color, ?_⟩
  intro e he d hd v hve hvd hcol
  have hc : f.edgeColor (e.image r) = f.edgeColor (d.image r) := by
    have hh := congrArg Fin.val hcol
    exact Fin.ext hh
  have hmap := f.edgeColor_proper (hrcard e he) (hrcard d hd)
    (mem_image.mpr ⟨v, hve, rfl⟩) (mem_image.mpr ⟨v, hvd, rfl⟩) hc
  have hh := congrArg (fun t => t.image Subtype.val) hmap
  simpa only [hrecover e he, hrecover d hd] using hh

theorem lift_triangle {H : SimpleGraph V} {S : Finset V} {q : Finset V}
    (hq : H.IsNClique 3 q) : (attached H S C).IsNClique 3 (lift q) := by
  constructor
  · intro a ha b hb hne
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
    exact hq.isClique hx hy (fun h => hne (congrArg Sum.inl h))
  · simpa using hq.card_eq

theorem cone_triangle {H : SimpleGraph V} {S : Finset V} {e : Finset V}
    (he : H.IsNClique 2 e) (heS : e ⊆ S) (color : Finset V → C) :
    (attached H S C).IsNClique 3 (cone color e) := by
  constructor
  · intro a ha b hb hne
    cases a with
    | inl a =>
      cases b with
      | inl b =>
          exact he.isClique (inl_mem_cone.mp ha) (inl_mem_cone.mp hb)
            (fun h => hne (congrArg Sum.inl h))
      | inr b => exact heS (inl_mem_cone.mp ha)
    | inr a =>
      cases b with
      | inl b => exact heS (inl_mem_cone.mp hb)
      | inr b => exact False.elim (hne (congrArg Sum.inr
          ((inr_mem_cone.mp ha).trans (inr_mem_cone.mp hb).symm)))
  · rw [cone_card, he.card_eq]

/-- Every graph packing can be compressed without losing any triangle. -/
theorem compress_packing (H : SimpleGraph V) (S : Finset V) (hs : 2 ≤ S.card)
    (P : Finset (Finset (V ⊕ C))) (hP : IsPacking (attached H S C) P) :
    ∃ R : Finset (Finset (V ⊕ Fin (colorCount S.card))),
      IsPacking (attached H S (Fin (colorCount S.card))) R ∧ R.card = P.card := by
  classical
  obtain ⟨Q, J, hQ, hJ, hJS, havoid, hcount⟩ := extract_packing hP
  have hJcard : ∀ e ∈ J, e.card = 2 := fun e he => (hJ e he).card_eq
  obtain ⟨color, hcolor⟩ := neighborhood_coloring S hs J hJcard hJS
  obtain ⟨R, hRcard, _, hRdis, hkeep, hcone⟩ := preserve_old_packing Q J
    (fun q hq => (hQ.1 q hq).card_eq) hQ.2 hJcard havoid color hcolor
  let A := Q.image (lift (C := Fin (colorCount S.card)))
  let B := J.image (cone color)
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro t ht hu
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
    obtain ⟨e, he, heq⟩ := mem_image.mp hu
    have hc : Sum.inr (color e) ∈ cone color e := by simp
    rw [heq] at hc
    exact inr_not_mem_lift hc
  have hcard : (A ∪ B).card = Q.card + J.card := by
    rw [card_union_of_disjoint hAB]
    change (Q.image (lift (C := Fin (colorCount S.card)))).card + (J.image (cone color)).card = _
    rw [card_image_of_injective Q lift_injective, card_image_of_injective J (cone_injective color)]
  have hsub : A ∪ B ⊆ R := by
    intro t ht
    rcases mem_union.mp ht with ht | ht
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
      exact hkeep q hq
    · obtain ⟨e, he, rfl⟩ := mem_image.mp ht
      exact hcone e he
  have heq : A ∪ B = R := eq_of_subset_of_card_le hsub (by rw [hRcard, hcard])
  refine ⟨R, ⟨?_, hRdis⟩, hRcard.trans hcount.symm⟩
  intro t ht
  rw [← heq] at ht
  rcases mem_union.mp ht with ht | ht
  · obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
    exact lift_triangle (hQ.1 q hq)
  · obtain ⟨e, he, rfl⟩ := mem_image.mp ht
    exact cone_triangle (hJ e he) (hJS e he) color

#print axioms extract_packing
#print axioms compress_packing
#check compress_packing

variable [DecidableEq W]

theorem image_injective {f : V → W} (hf : Function.Injective f) :
    Function.Injective (fun t : Finset V => t.image f) := by
  intro t u h
  ext v
  have mem_image_iff : ∀ s : Finset V, f v ∈ s.image f ↔ v ∈ s := by
    intro s
    constructor
    · intro hv
      obtain ⟨x, hx, hfx⟩ := mem_image.mp hv
      have hxf : x = v := hf hfx
      simpa [hxf] using hx
    · intro hv
      exact mem_image.mpr ⟨v, hv, rfl⟩
  have hh := congrArg (fun s => f v ∈ s) h
  exact (mem_image_iff t).symm.trans ((iff_of_eq hh).trans (mem_image_iff u))

theorem pair_subset_from_mem {a b : V} {t : Finset V} (ha : a ∈ t) (hb : b ∈ t) :
    ({a, b} : Finset V) ⊆ t := by
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl <;> assumption

/-- Injective graph maps preserve triangle packings and their exact sizes. -/
theorem map_packing {H : SimpleGraph V} {K : SimpleGraph W} (f : V → W)
    (hf : Function.Injective f) (hadj : ∀ a b, H.Adj a b → K.Adj (f a) (f b))
    {P : Finset (Finset V)} (hP : IsPacking H P) :
    ∃ R : Finset (Finset W), IsPacking K R ∧ R.card = P.card := by
  refine ⟨P.image (fun t => t.image f), ⟨?_, ?_⟩,
    card_image_of_injective P (image_injective hf)⟩
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
    constructor
    · intro a ha b hb hne
      obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
      exact hadj x y ((hP.1 q hq).isClique hx hy (fun h => hne (congrArg f h)))
    · rw [card_image_of_injective q hf, (hP.1 q hq).card_eq]
  · intro t ht u hu hne
    obtain ⟨t0, ht0, rfl⟩ := mem_image.mp ht
    obtain ⟨u0, hu0, rfl⟩ := mem_image.mp hu
    apply disjoint_left.mpr
    intro e het heu
    obtain ⟨het', he⟩ := mem_powersetCard.mp het
    obtain ⟨heu', _⟩ := mem_powersetCard.mp heu
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp he
    have hat := het' (by simp : a ∈ ({a, b} : Finset W))
    have hbt := het' (by simp : b ∈ ({a, b} : Finset W))
    have hau := heu' (by simp : a ∈ ({a, b} : Finset W))
    have hbu := heu' (by simp : b ∈ ({a, b} : Finset W))
    obtain ⟨x, hxt, rfl⟩ := mem_image.mp hat
    obtain ⟨y, hyt, rfl⟩ := mem_image.mp hbt
    have hxu : x ∈ u0 := by
      obtain ⟨z, hz, hzx⟩ := mem_image.mp hau
      simpa [hf hzx] using hz
    have hyu : y ∈ u0 := by
      obtain ⟨z, hz, hzy⟩ := mem_image.mp hbu
      simpa [hf hzy] using hz
    have hxy : x ≠ y := fun h => hab (congrArg f h)
    have hne0 : t0 ≠ u0 := fun h => hne (congrArg (fun s : Finset V => s.image f) h)
    exact disjoint_left.mp (hP.2 ht0 hu0 hne0)
      (mem_powersetCard.mpr ⟨pair_subset_from_mem hxt hyt, card_pair hxy⟩)
      (mem_powersetCard.mpr ⟨pair_subset_from_mem hxu hyu, card_pair hxy⟩)

def centerMap (f : C → D) : V ⊕ C → V ⊕ D
  | .inl v => .inl v
  | .inr c => .inr (f c)

theorem centerMap_injective {f : C → D} (hf : Function.Injective f) :
    Function.Injective (centerMap (V := V) f) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Sum.inl.inj h)
    | inr b => cases h
  | inr a =>
    cases b with
    | inl b => cases h
    | inr b => exact congrArg Sum.inr (hf (Sum.inr.inj h))

theorem centerMap_adj (H : SimpleGraph V) (S : Finset V) (f : C → D)
    (a b : V ⊕ C) (h : (attached H S C).Adj a b) :
    (attached H S D).Adj (centerMap f a) (centerMap f b) := by
  cases a <;> cases b <;> exact h

theorem increase_centers (H : SimpleGraph V) (S : Finset V) {m n : ℕ}
    (hmn : m ≤ n) {P : Finset (Finset (V ⊕ Fin m))} (hP : IsPacking (attached H S (Fin m)) P) :
    ∃ R : Finset (Finset (V ⊕ Fin n)), IsPacking (attached H S (Fin n)) R ∧ R.card = P.card := by
  let f : Fin m → Fin n := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun x : Fin n => x.val) h
  exact map_packing (centerMap f) (centerMap_injective hf) (centerMap_adj H S f) hP

def CanPack (H : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ P : Finset (Finset V), IsPacking H P ∧ P.card = n

/-- Compression preserves every attainable packing size, not just an upper bound. -/
theorem packing_sizes_attached_min (H : SimpleGraph V) (S : Finset V) (hs : 2 ≤ S.card)
    (m n : ℕ) : CanPack (attached H S (Fin m)) n ↔
      CanPack (attached H S (Fin (min m (colorCount S.card)))) n := by
  by_cases hm : m ≤ colorCount S.card
  · rw [Nat.min_eq_left hm]
  · have hh : colorCount S.card ≤ m := by omega
    rw [Nat.min_eq_right hh]
    constructor
    · rintro ⟨P, hP, hc⟩
      obtain ⟨R, hR, hRc⟩ := compress_packing H S hs P hP
      exact ⟨R, hR, hRc.trans hc⟩
    · rintro ⟨P, hP, hc⟩
      obtain ⟨R, hR, hRc⟩ := increase_centers H S hh hP
      exact ⟨R, hR, hRc.trans hc⟩

/-- The maximum cardinality over all triangle packings of a finite graph. -/
noncomputable def packingNumber [Fintype V] (H : SimpleGraph V) : ℕ := by
  classical
  exact ((univ : Finset (Finset (Finset V))).filter (IsPacking H)).sup Finset.card

theorem packingNumber_spec [Fintype V] (H : SimpleGraph V) :
    ∃ P : Finset (Finset V), IsPacking H P ∧ P.card = packingNumber H ∧
      ∀ Q : Finset (Finset V), IsPacking H Q → Q.card ≤ packingNumber H := by
  classical
  let A := (univ : Finset (Finset (Finset V))).filter (IsPacking H)
  have hA : A.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [A, IsPacking]
  obtain ⟨P, hP, hmax⟩ := exists_max_image A Finset.card hA
  have hle : A.sup Finset.card ≤ P.card := Finset.sup_le hmax
  have hge : P.card ≤ A.sup Finset.card := le_sup hP
  refine ⟨P, (mem_filter.mp hP).2, le_antisymm hge hle, ?_⟩
  intro Q hQ
  exact le_sup (show Q ∈ A by simp [A, hQ])

/-- Exact equality of the optimal packing numbers, for all multiplicities. -/
theorem packingNumber_attached_min [Fintype V] (H : SimpleGraph V) (S : Finset V)
    (hs : 2 ≤ S.card) (m : ℕ) : packingNumber (attached H S (Fin m)) =
      packingNumber (attached H S (Fin (min m (colorCount S.card)))) := by
  classical
  obtain ⟨P, hP, hPc, hPmax⟩ := packingNumber_spec (attached H S (Fin m))
  obtain ⟨R, hR, hRc, hRmax⟩ := packingNumber_spec
    (attached H S (Fin (min m (colorCount S.card))))
  apply le_antisymm
  · have hc : CanPack (attached H S (Fin m)) P.card := ⟨P, hP, rfl⟩
    obtain ⟨Q, hQ, hQc⟩ := (packing_sizes_attached_min H S hs m P.card).mp hc
    have hh := hRmax Q hQ
    simpa only [hQc, hPc] using hh
  · have hc : CanPack (attached H S (Fin (min m (colorCount S.card)))) R.card := ⟨R, hR, rfl⟩
    obtain ⟨Q, hQ, hQc⟩ := (packing_sizes_attached_min H S hs m R.card).mpr hc
    have hh := hPmax Q hQ
    simpa only [hQc, hRc] using hh

#print axioms map_packing
#print axioms packing_sizes_attached_min
#print axioms packingNumber_spec
#print axioms packingNumber_attached_min
#check packingNumber_attached_min
end TuzaGraphCompression

/-!
Uniform matching classes and explicit clique-neighborhood allocation.
OpenAI Codex (GPT-6 Astra), 2026-10-07.
-/
namespace TuzaMatchingClasses
open Finset TuzaCompression TuzaGraphCompression

variable {V C : Type*} [DecidableEq V] [DecidableEq C]

/-- Disjoint two-element sets use two distinct vertices each. -/
theorem matching_card_le (S : Finset V) (M : Finset (Finset V))
    (hcard : ∀ e ∈ M, e.card = 2) (hsub : ∀ e ∈ M, e ⊆ S)
    (hdis : (M : Set (Finset V)).PairwiseDisjoint id) : M.card ≤ S.card / 2 := by
  have hcount : (M.biUnion id).card = 2 * M.card := by
    rw [card_biUnion hdis]
    calc
      (∑ e ∈ M, e.card) = ∑ e ∈ M, 2 := sum_congr rfl (fun e he => hcard e he)
      _ = 2 * M.card := by simp [mul_comm]
  have hu : M.biUnion id ⊆ S := by
    intro v hv
    obtain ⟨e, he, hve⟩ := mem_biUnion.mp hv
    exact hsub e he hve
  have hh := card_le_card hu
  rw [hcount] at hh
  omega

/-- The complete edge set exactly fills h(s) matchings of capacity floor(s/2). -/
theorem palette_capacity (s : ℕ) : s.choose 2 = colorCount s * (s / 2) := by
  by_cases he : s % 2 = 0
  · have hs : s = 2 * (s / 2) := by omega
    have hm : s * (s - 1) = ((s - 1) * (s / 2)) * 2 := by
      calc
        s * (s - 1) = (2 * (s / 2)) * (s - 1) := congrArg (fun n => n * (s - 1)) hs
        _ = ((s - 1) * (s / 2)) * 2 := by ring
    rw [Nat.choose_two_right, hm]
    simp [colorCount, he]
  · have hs : s - 1 = 2 * (s / 2) := by omega
    have hm : s * (s - 1) = (s * (s / 2)) * 2 := by rw [hs]; ring
    rw [Nat.choose_two_right, hm]
    simp [colorCount, he]

def ProperOn (S : Finset V) (color : Finset V → C) : Prop :=
  ∀ e ∈ S.powersetCard 2, ∀ d ∈ S.powersetCard 2,
    ∀ v ∈ e, v ∈ d → color e = color d → e = d

def colorClass (S : Finset V) (color : Finset V → C) (c : C) : Finset (Finset V) :=
  (S.powersetCard 2).filter (fun e => color e = c)

theorem class_card_le (S : Finset V) (color : Finset V → C)
    (hproper : ProperOn S color) (c : C) : (colorClass S color c).card ≤ S.card / 2 := by
  apply matching_card_le S
  · intro e he
    exact (mem_powersetCard.mp (mem_filter.mp he).1).2
  · intro e he
    exact (mem_powersetCard.mp (mem_filter.mp he).1).1
  · intro e he d hd hne
    apply disjoint_left.mpr
    intro v hve hvd
    exact hne (hproper e (mem_filter.mp he).1 d (mem_filter.mp hd).1 v hve hvd
      ((mem_filter.mp he).2.trans (mem_filter.mp hd).2.symm))

/-- Every class is full in every proper coloring with the sharp palette size. -/
theorem uniform_class_size (S : Finset V) (color : Finset V → Fin (colorCount S.card))
    (hproper : ProperOn S color) (c : Fin (colorCount S.card)) :
    (colorClass S color c).card = S.card / 2 := by
  classical
  have htotal : (∑ d : Fin (colorCount S.card), (colorClass S color d).card) =
      colorCount S.card * (S.card / 2) := by
    calc
      (∑ d : Fin (colorCount S.card), (colorClass S color d).card) =
          (S.powersetCard 2).card :=
        (card_eq_sum_card_fiberwise (t := univ) (fun _ _ => mem_univ _)).symm
      _ = S.card.choose 2 := by simp
      _ = colorCount S.card * (S.card / 2) := palette_capacity _
  by_contra hne
  have hle := class_card_le S color hproper c
  have hlt : (colorClass S color c).card < S.card / 2 := by omega
  have hsum : (∑ d : Fin (colorCount S.card), (colorClass S color d).card) <
      ∑ _d : Fin (colorCount S.card), S.card / 2 :=
    sum_lt_sum (fun d _ => class_card_le S color hproper d) ⟨c, mem_univ _, hlt⟩
  have hconst : (∑ _d : Fin (colorCount S.card), S.card / 2) =
      colorCount S.card * (S.card / 2) := by simp
  omega

def selectedEdges (S : Finset V) (color : Finset V → C) (A : Finset C) : Finset (Finset V) :=
  (S.powersetCard 2).filter (fun e => color e ∈ A)

/-- Every chosen palette, without averaging, supplies its exact share of edges. -/
theorem selected_edges_card (S : Finset V) (color : Finset V → Fin (colorCount S.card))
    (hproper : ProperOn S color) (A : Finset (Fin (colorCount S.card))) :
    (selectedEdges S color A).card = A.card * (S.card / 2) := by
  classical
  calc
    (selectedEdges S color A).card = ∑ c ∈ A, (colorClass S color c).card :=
      (sum_card_fiberwise_eq_card_filter (S.powersetCard 2) A color).symm
    _ = ∑ _c ∈ A, S.card / 2 := sum_congr rfl (fun c _ => uniform_class_size S color hproper c)
    _ = A.card * (S.card / 2) := by simp

/-- Assign each selected matching to a distinct real center in an attached graph. -/
theorem palette_packing [Nonempty C] (H : SimpleGraph V) (S : Finset V)
    (hS : H.IsClique S) (color : Finset V → Fin (colorCount S.card))
    (hproper : ProperOn S color) (A : Finset (Fin (colorCount S.card)))
    (g : A → C) (hg : Function.Injective g) :
    ∃ P : Finset (Finset (V ⊕ C)), IsPacking (attached H S C) P ∧
      P.card = A.card * (S.card / 2) ∧ ∀ t ∈ P, t.toRight.Nonempty := by
  classical
  let J := selectedEdges S color A
  let chosen : Finset V → C := fun e =>
    if hc : color e ∈ A then g ⟨color e, hc⟩ else Classical.choice ‹Nonempty C›
  have hJcard : ∀ e ∈ J, e.card = 2 := fun e he =>
    (mem_powersetCard.mp (mem_filter.mp he).1).2
  have hJS : ∀ e ∈ J, e ⊆ S := fun e he =>
    (mem_powersetCard.mp (mem_filter.mp he).1).1
  have hchosen : ∀ e ∈ J, ∀ d ∈ J, ∀ v ∈ e, v ∈ d → chosen e = chosen d → e = d := by
    intro e he d hd v hve hvd hc
    have heA := (mem_filter.mp he).2
    have hdA := (mem_filter.mp hd).2
    have hh : g ⟨color e, heA⟩ = g ⟨color d, hdA⟩ := by
      simpa only [chosen, dif_pos heA, dif_pos hdA] using hc
    exact hproper e (mem_filter.mp he).1 d (mem_filter.mp hd).1 v hve hvd
      (congrArg Subtype.val (hg hh))
  refine ⟨J.image (cone chosen), ⟨?_, cones_edge_disjoint J hJcard chosen hchosen⟩, ?_, ?_⟩
  · intro t ht
    obtain ⟨e, he, rfl⟩ := mem_image.mp ht
    have heH : H.IsNClique 2 e := ⟨by
      intro a ha b hb hne
      exact hS (hJS e he ha) (hJS e he hb) hne, hJcard e he⟩
    exact cone_triangle heH (hJS e he) chosen
  · rw [card_image_of_injective J (cone_injective chosen)]
    exact selected_edges_card S color hproper A
  · intro t ht
    obtain ⟨e, he, rfl⟩ := mem_image.mp ht
    exact ⟨chosen e, mem_toRight.mpr (by simp)⟩

/-- Uniform allocation on any clique neighborhood, for every multiplicity m. -/
theorem clique_neighborhood_packing (H : SimpleGraph V) (S : Finset V)
    (hs : 2 ≤ S.card) (hS : H.IsClique S) (m : ℕ) :
    ∃ P : Finset (Finset (V ⊕ Fin m)), IsPacking (attached H S (Fin m)) P ∧
      P.card = min m (colorCount S.card) * (S.card / 2) ∧
      ∀ t ∈ P, t.toRight.Nonempty := by
  classical
  by_cases hm : m = 0
  · subst m
    refine ⟨∅, ?_, by simp, ?_⟩
    · simp [IsPacking]
    · simp
  · letI : NeZero m := ⟨hm⟩
    obtain ⟨color, hproper⟩ := neighborhood_coloring S hs (S.powersetCard 2)
      (fun e he => (mem_powersetCard.mp he).2) (fun e he => (mem_powersetCard.mp he).1)
    obtain ⟨A, _hA, hAcard⟩ := exists_subset_card_eq
      (show min m (colorCount S.card) ≤ (univ : Finset (Fin (colorCount S.card))).card by simp)
    have hAm : A.card ≤ m := by rw [hAcard]; exact Nat.min_le_left _ _
    let ec : A ≃ Fin A.card := Fintype.equivOfCardEq (by simp)
    let g : A → Fin m := fun a => ⟨(ec a).val, Nat.lt_of_lt_of_le (ec a).isLt hAm⟩
    have hg : Function.Injective g := by
      intro a b hh
      apply ec.injective
      apply Fin.ext
      exact congrArg (fun c : Fin m => c.val) hh
    obtain ⟨P, hP, hcount, hout⟩ := palette_packing H S hS color hproper A g hg
    exact ⟨P, hP, by simpa only [hAcard] using hcount, hout⟩

/-- The explicit allocation gives a lower bound on the actual graph optimum. -/
theorem clique_neighborhood_lower_bound [Fintype V] (H : SimpleGraph V) (S : Finset V)
    (hs : 2 ≤ S.card) (hS : H.IsClique S) (m : ℕ) :
    min m (colorCount S.card) * (S.card / 2) ≤ packingNumber (attached H S (Fin m)) := by
  obtain ⟨P, hP, hcount, _⟩ := clique_neighborhood_packing H S hs hS m
  obtain ⟨Q, hQ, hQc, hmax⟩ := packingNumber_spec (attached H S (Fin m))
  simpa only [hcount] using hmax P hP

#print axioms matching_card_le
#print axioms palette_capacity
#print axioms uniform_class_size
#print axioms selected_edges_card
#print axioms palette_packing
#print axioms clique_neighborhood_packing
#print axioms clique_neighborhood_lower_bound
#check clique_neighborhood_packing
#check clique_neighborhood_lower_bound
end TuzaMatchingClasses

/-!
Deterministic palette selection, overlap control and a two-neighborhood graph packing.
OpenAI Codex (GPT-6 Astra), 2026-10-07.
-/
namespace TuzaIndependentAllocation
open Finset TuzaCompression TuzaGraphCompression TuzaMatchingClasses

variable {α V C D : Type*} [DecidableEq α] [DecidableEq V] [DecidableEq C] [DecidableEq D]

/-- Select r elements whose weights are no larger than every unselected weight. -/
theorem ordered_subset (w : α → ℕ) (r : ℕ) (s : Finset α) (hr : r ≤ s.card) :
    ∃ A ⊆ s, A.card = r ∧ ∀ a ∈ A, ∀ b ∈ s, b ∉ A → w a ≤ w b := by
  classical
  induction r generalizing s with
  | zero => exact ⟨∅, empty_subset _, by simp, by simp⟩
  | succ r ih =>
    have hs : s.Nonempty := card_pos.mp (by omega)
    obtain ⟨x, hx, hmin⟩ := exists_min_image s w hs
    obtain ⟨A, hAs, hAc, horder⟩ := ih (s.erase x) (by rw [card_erase_of_mem hx]; omega)
    have hxA : x ∉ A := fun h => (mem_erase.mp (hAs h)).1 rfl
    refine ⟨insert x A, ?_, ?_, ?_⟩
    · intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · exact hx
      · exact (mem_erase.mp (hAs ha)).2
    · rw [card_insert_of_notMem hxA, hAc]
    · intro a ha b hb hbA
      rcases mem_insert.mp ha with rfl | ha
      · exact hmin b hb
      · have hbx : b ≠ x := by
          intro hh
          apply hbA
          simp [hh]
        have hbA' : b ∉ A := fun hh => hbA (mem_insert_of_mem hh)
        exact horder a ha b (mem_erase.mpr ⟨hbx, hb⟩) hbA'

/-- The r smallest weights have at most r/|s| of the total, in integer form. -/
theorem weighted_subset (w : α → ℕ) (r : ℕ) (s : Finset α) (hr : r ≤ s.card) :
    ∃ A ⊆ s, A.card = r ∧ s.card * (∑ a ∈ A, w a) ≤ r * (∑ a ∈ s, w a) := by
  obtain ⟨A, hAs, hAc, horder⟩ := ordered_subset w r s hr
  let B := s \ A
  have hdis : Disjoint A B := by
    apply disjoint_left.mpr
    intro a ha hb
    exact (mem_sdiff.mp hb).2 ha
  have hunion : A ∪ B = s := by
    ext a
    simp only [B, mem_union, mem_sdiff]
    constructor
    · rintro (ha | ⟨ha, _⟩)
      · exact hAs ha
      · exact ha
    · intro ha
      by_cases h : a ∈ A
      · exact Or.inl h
      · exact Or.inr ⟨ha, h⟩
  have hcard : s.card = A.card + B.card := by rw [← hunion, card_union_of_disjoint hdis]
  have hsum : (∑ a ∈ s, w a) = (∑ a ∈ A, w a) + ∑ b ∈ B, w b := by
    rw [← hunion, sum_union hdis]
  have hcross : B.card * (∑ a ∈ A, w a) ≤ A.card * (∑ b ∈ B, w b) := by
    calc
      B.card * (∑ a ∈ A, w a) = ∑ a ∈ A, ∑ _b ∈ B, w a := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro a ha
        simp
      _ ≤ ∑ _a ∈ A, ∑ b ∈ B, w b := by
        apply sum_le_sum
        intro a ha
        apply sum_le_sum
        intro b hb
        exact horder a ha b (mem_sdiff.mp hb).1 (mem_sdiff.mp hb).2
      _ = A.card * (∑ b ∈ B, w b) := by simp
  refine ⟨A, hAs, hAc, ?_⟩
  calc
    s.card * (∑ a ∈ A, w a) = A.card * (∑ a ∈ A, w a) + B.card * (∑ a ∈ A, w a) := by rw [hcard]; ring
    _ ≤ A.card * (∑ a ∈ A, w a) + A.card * (∑ b ∈ B, w b) := Nat.add_le_add_left hcross _
    _ = r * (∑ a ∈ s, w a) := by rw [hsum, hAc]; ring

/-- Pick a palette that meets a marked edge family no more often than average. -/
theorem choose_colors {h : ℕ} (E : Finset α) (color : α → Fin h) (p : ℕ) (hp : p ≤ h) :
    ∃ A : Finset (Fin h), A.card = p ∧
      h * (E.filter (fun e => color e ∈ A)).card ≤ p * E.card := by
  classical
  let w := fun c : Fin h => (E.filter (fun e => color e = c)).card
  obtain ⟨A, _, hAc, hcost⟩ := weighted_subset w p univ (by simpa using hp)
  have hall : (∑ c : Fin h, w c) = E.card :=
    (card_eq_sum_card_fiberwise (t := univ) (fun _ _ => mem_univ _)).symm
  have hsel : (∑ c ∈ A, w c) = (E.filter (fun e => color e ∈ A)).card :=
    sum_card_fiberwise_eq_card_filter E A color
  exact ⟨A, hAc, by simpa only [card_univ, Fintype.card_fin, hall, hsel] using hcost⟩

/-- Two deterministic choices give the product bound on the overlap. -/
theorem select_two_palettes {a b : ℕ} (E F : Finset α)
    (f : α → Fin a) (g : α → Fin b) (p q : ℕ) (hp : p ≤ a) (hq : q ≤ b) :
    ∃ A : Finset (Fin a), ∃ B : Finset (Fin b), A.card = p ∧ B.card = q ∧
      a * b * ((E.filter (fun e => f e ∈ A)) ∩ (F.filter (fun e => g e ∈ B))).card
        ≤ p * q * (E ∩ F).card := by
  classical
  obtain ⟨A, hAc, hA⟩ := choose_colors (E ∩ F) f p hp
  let J := E.filter (fun e => f e ∈ A)
  have hfirst : (E ∩ F).filter (fun e => f e ∈ A) = J ∩ F := by
    ext e
    simp only [J, mem_filter, mem_inter]
    tauto
  rw [hfirst] at hA
  obtain ⟨B, hBc, hB⟩ := choose_colors (J ∩ F) g q hq
  have hsecond : (J ∩ F).filter (fun e => g e ∈ B) = J ∩ F.filter (fun e => g e ∈ B) := by
    ext e
    simp only [mem_filter, mem_inter]
    tauto
  rw [hsecond] at hB
  refine ⟨A, B, hAc, hBc, ?_⟩
  calc
    a * b * (J ∩ F.filter (fun e => g e ∈ B)).card =
        a * (b * (J ∩ F.filter (fun e => g e ∈ B)).card) := by ring
    _ ≤ a * (q * (J ∩ F).card) := Nat.mul_le_mul_left a hB
    _ = q * (a * (J ∩ F).card) := by ring
    _ ≤ q * (p * (E ∩ F).card) := Nat.mul_le_mul_left q hA
    _ = p * q * (E ∩ F).card := by ring

def neighborhood (S T : Finset V) : C ⊕ D → Finset V := Sum.elim (fun _ => S) (fun _ => T)

def twoAttached (H : SimpleGraph V) (S T : Finset V) (C D : Type*) : SimpleGraph (V ⊕ (C ⊕ D)) where
  Adj a b := match a, b with
    | .inl v, .inl w => H.Adj v w
    | .inl v, .inr c => v ∈ neighborhood S T c
    | .inr c, .inl v => v ∈ neighborhood S T c
    | .inr _, .inr _ => False
  symm.symm a b h := by
    cases a <;> cases b
    · exact H.adj_symm h
    · exact h
    · exact h
    · exact h
  loopless.irrefl a := by
    cases a
    · exact H.irrefl
    · exact id

theorem cone_two_triangle {H : SimpleGraph V} {S T : Finset V} {e : Finset V}
    (he : H.IsNClique 2 e) (color : Finset V → C ⊕ D)
    (heN : e ⊆ neighborhood S T (color e)) :
    (twoAttached H S T C D).IsNClique 3 (cone color e) := by
  constructor
  · intro a ha b hb hne
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        exact he.isClique (inl_mem_cone.mp ha) (inl_mem_cone.mp hb)
          (fun h => hne (congrArg Sum.inl h))
      | inr b =>
        have hb' := inr_mem_cone.mp hb
        subst b
        exact heN (inl_mem_cone.mp ha)
    | inr a =>
      cases b with
      | inl b =>
        have ha' := inr_mem_cone.mp ha
        subst a
        exact heN (inl_mem_cone.mp hb)
      | inr b => exact False.elim (hne (congrArg Sum.inr
          ((inr_mem_cone.mp ha).trans (inr_mem_cone.mp hb).symm)))
  · rw [cone_card, he.card_eq]

/-- Inject any selected finite palette into the available centers, including empty palettes. -/
theorem embed_palette (A : Finset C) (m : ℕ) (hA : A.card ≤ m) :
    ∃ g : A → Fin m, Function.Injective g := by
  classical
  let ec : A ≃ Fin A.card := Fintype.equivOfCardEq (by simp)
  let g : A → Fin m := fun a => ⟨(ec a).val, Nat.lt_of_lt_of_le (ec a).isLt hA⟩
  refine ⟨g, ?_⟩
  intro a b h
  apply ec.injective
  apply Fin.ext
  exact congrArg (fun c : Fin m => c.val) h

/-- Merge two colored edge sets, giving each shared edge to the first type exactly once. -/
theorem merge_palettes [Nonempty (C ⊕ D)] (H : SimpleGraph V) (S T : Finset V)
    (hS : H.IsClique S) (hT : H.IsClique T)
    (f : Finset V → Fin (colorCount S.card)) (g : Finset V → Fin (colorCount T.card))
    (hf : ProperOn S f) (hg : ProperOn T g)
    (A : Finset (Fin (colorCount S.card))) (B : Finset (Fin (colorCount T.card)))
    (ca : A → C) (cb : B → D) (hca : Function.Injective ca) (hcb : Function.Injective cb) :
    ∃ P : Finset (Finset (V ⊕ (C ⊕ D))), IsPacking (twoAttached H S T C D) P ∧
      P.card = (selectedEdges S f A ∪ selectedEdges T g B).card ∧
      ∀ t ∈ P, t.toRight.Nonempty := by
  classical
  let J := selectedEdges S f A
  let K := selectedEdges T g B
  let chosen : Finset V → C ⊕ D := fun e =>
    if he : e ∈ J then Sum.inl (ca ⟨f e, (mem_filter.mp he).2⟩)
    else if he : e ∈ K then Sum.inr (cb ⟨g e, (mem_filter.mp he).2⟩)
    else Classical.choice ‹Nonempty (C ⊕ D)›
  have hleft (e) (he : e ∈ J) : chosen e = Sum.inl (ca ⟨f e, (mem_filter.mp he).2⟩) := by
    simp [chosen, he]
  have hright (e) (he : e ∉ J) (hk : e ∈ K) : chosen e = Sum.inr (cb ⟨g e, (mem_filter.mp hk).2⟩) := by
    simp [chosen, he, hk]
  have hproper : ∀ e ∈ J ∪ K, ∀ d ∈ J ∪ K, ∀ v ∈ e, v ∈ d → chosen e = chosen d → e = d := by
    intro e he d hd v hve hvd hc
    by_cases heJ : e ∈ J <;> by_cases hdJ : d ∈ J
    · rw [hleft e heJ, hleft d hdJ] at hc
      exact hf e (mem_filter.mp heJ).1 d (mem_filter.mp hdJ).1 v hve hvd
        (congrArg Subtype.val (hca (Sum.inl.inj hc)))
    · have hdK := (mem_union.mp hd).resolve_left hdJ
      rw [hleft e heJ, hright d hdJ hdK] at hc
      cases hc
    · have heK := (mem_union.mp he).resolve_left heJ
      rw [hright e heJ heK, hleft d hdJ] at hc
      cases hc
    · have heK := (mem_union.mp he).resolve_left heJ
      have hdK := (mem_union.mp hd).resolve_left hdJ
      rw [hright e heJ heK, hright d hdJ hdK] at hc
      exact hg e (mem_filter.mp heK).1 d (mem_filter.mp hdK).1 v hve hvd
        (congrArg Subtype.val (hcb (Sum.inr.inj hc)))
  have hcard : ∀ e ∈ J ∪ K, e.card = 2 := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact (mem_powersetCard.mp (mem_filter.mp he).1).2
    · exact (mem_powersetCard.mp (mem_filter.mp he).1).2
  refine ⟨(J ∪ K).image (cone chosen), ⟨?_, cones_edge_disjoint _ hcard chosen hproper⟩,
    card_image_of_injective _ (cone_injective chosen), ?_⟩
  · intro t ht
    obtain ⟨e, he, rfl⟩ := mem_image.mp ht
    by_cases heJ : e ∈ J
    · have heS := (mem_powersetCard.mp (mem_filter.mp heJ).1).1
      have heH : H.IsNClique 2 e := ⟨by
        intro a ha b hb hne
        exact hS (heS ha) (heS hb) hne, hcard e he⟩
      apply cone_two_triangle heH chosen
      rw [hleft e heJ]
      exact heS
    · have heK := (mem_union.mp he).resolve_left heJ
      have heT := (mem_powersetCard.mp (mem_filter.mp heK).1).1
      have heH : H.IsNClique 2 e := ⟨by
        intro a ha b hb hne
        exact hT (heT ha) (heT hb) hne, hcard e he⟩
      apply cone_two_triangle heH chosen
      rw [hright e heJ heK]
      exact heT
  · intro t ht
    obtain ⟨e, he, rfl⟩ := mem_image.mp ht
    exact ⟨chosen e, mem_toRight.mpr (by simp)⟩

theorem common_edges (S T : Finset V) :
    S.powersetCard 2 ∩ T.powersetCard 2 = (S ∩ T).powersetCard 2 := by
  ext e
  simp only [mem_inter, mem_powersetCard]
  constructor
  · rintro ⟨⟨hS, hc⟩, ⟨hT, _⟩⟩
    exact ⟨fun v hv => mem_inter.mpr ⟨hS hv, hT hv⟩, hc⟩
  · rintro ⟨hST, hc⟩
    exact ⟨⟨fun v hv => (mem_inter.mp (hST hv)).1, hc⟩,
      ⟨fun v hv => (mem_inter.mp (hST hv)).2, hc⟩⟩

/-- The independent allocation bound, with positive denominators cleared, for actual graphs. -/
theorem independent_allocation (H : SimpleGraph V) (S T : Finset V)
    (hs : 2 ≤ S.card) (ht : 2 ≤ T.card) (hS : H.IsClique S) (hT : H.IsClique T) (m n : ℕ) :
    ∃ P : Finset (Finset (V ⊕ (Fin m ⊕ Fin n))), IsPacking (twoAttached H S T (Fin m) (Fin n)) P ∧
      colorCount T.card * min m (colorCount S.card) * S.card.choose 2 +
        colorCount S.card * min n (colorCount T.card) * T.card.choose 2 ≤
      colorCount S.card * colorCount T.card * P.card +
        min m (colorCount S.card) * min n (colorCount T.card) * (S ∩ T).card.choose 2 ∧
      ∀ t ∈ P, t.toRight.Nonempty := by
  classical
  by_cases hz : m = 0 ∧ n = 0
  · rcases hz with ⟨rfl, rfl⟩
    exact ⟨∅, by simp [IsPacking], by simp, by simp⟩
  · letI : Nonempty (Fin m ⊕ Fin n) := by
      by_cases hm : m = 0
      · exact ⟨Sum.inr ⟨0, by omega⟩⟩
      · exact ⟨Sum.inl ⟨0, by omega⟩⟩
    obtain ⟨f, hf⟩ := neighborhood_coloring S hs (S.powersetCard 2)
      (fun e he => (mem_powersetCard.mp he).2) (fun e he => (mem_powersetCard.mp he).1)
    obtain ⟨g, hg⟩ := neighborhood_coloring T ht (T.powersetCard 2)
      (fun e he => (mem_powersetCard.mp he).2) (fun e he => (mem_powersetCard.mp he).1)
    let a := colorCount S.card
    let b := colorCount T.card
    let p := min m a
    let q := min n b
    obtain ⟨A, B, hAc, hBc, hcost⟩ := select_two_palettes (S.powersetCard 2) (T.powersetCard 2)
      f g p q (Nat.min_le_right _ _) (Nat.min_le_right _ _)
    obtain ⟨ca, hca⟩ := embed_palette A m (by rw [hAc]; exact Nat.min_le_left _ _)
    obtain ⟨cb, hcb⟩ := embed_palette B n (by rw [hBc]; exact Nat.min_le_left _ _)
    obtain ⟨P, hP, hPc, hout⟩ := merge_palettes H S T hS hT f g hf hg A B ca cb hca hcb
    let J := selectedEdges S f A
    let K := selectedEdges T g B
    have hcost' : a * b * (J ∩ K).card ≤ p * q * (S ∩ T).card.choose 2 := by
      simpa [a, b, J, K, selectedEdges, common_edges] using hcost
    have hJc : J.card = p * (S.card / 2) := by
      rw [show J = selectedEdges S f A from rfl, selected_edges_card S f hf, hAc]
    have hKc : K.card = q * (T.card / 2) := by
      rw [show K = selectedEdges T g B from rfl, selected_edges_card T g hg, hBc]
    have hcount : P.card + (J ∩ K).card = p * (S.card / 2) + q * (T.card / 2) := by
      rw [hPc]
      exact (card_union_add_card_inter J K).trans (congrArg₂ Nat.add hJc hKc)
    refine ⟨P, hP, ?_, hout⟩
    change b * p * S.card.choose 2 + a * q * T.card.choose 2 ≤
      a * b * P.card + p * q * (S ∩ T).card.choose 2
    calc
      b * p * S.card.choose 2 + a * q * T.card.choose 2 =
          a * b * (p * (S.card / 2) + q * (T.card / 2)) := by
        rw [palette_capacity S.card, palette_capacity T.card]
        change b * p * (a * (S.card / 2)) + a * q * (b * (T.card / 2)) = _
        ring
      _ = a * b * (P.card + (J ∩ K).card) := by rw [hcount]
      _ = a * b * P.card + a * b * (J ∩ K).card := by ring
      _ ≤ a * b * P.card + p * q * (S ∩ T).card.choose 2 := Nat.add_le_add_left hcost' _

/-- The same bound for the attained maximum packing number of the finite graph. -/
theorem independent_allocation_bound [Fintype V] (H : SimpleGraph V) (S T : Finset V)
    (hs : 2 ≤ S.card) (ht : 2 ≤ T.card) (hS : H.IsClique S) (hT : H.IsClique T) (m n : ℕ) :
      colorCount T.card * min m (colorCount S.card) * S.card.choose 2 +
        colorCount S.card * min n (colorCount T.card) * T.card.choose 2 ≤
      colorCount S.card * colorCount T.card * packingNumber (twoAttached H S T (Fin m) (Fin n)) +
        min m (colorCount S.card) * min n (colorCount T.card) * (S ∩ T).card.choose 2 := by
  obtain ⟨P, hP, hb, _⟩ := independent_allocation H S T hs ht hS hT m n
  obtain ⟨Q, hQ, hQc, hmax⟩ := packingNumber_spec (twoAttached H S T (Fin m) (Fin n))
  exact hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (hmax P hP)) _)

#print axioms ordered_subset
#print axioms weighted_subset
#print axioms choose_colors
#print axioms select_two_palettes
#print axioms merge_palettes
#print axioms independent_allocation
#print axioms independent_allocation_bound
#check independent_allocation_bound
end TuzaIndependentAllocation


/-! Coherent neighborhood colors and cyclic finite averaging.
OpenAI Codex (GPT-6 Astra), 2026-10-07. -/
namespace TuzaCoupledAllocation
open Finset TuzaCompression TuzaGraphCompression TuzaMatchingClasses TuzaIndependentAllocation
variable {V C D X Y : Type*} [DecidableEq V] [DecidableEq C] [DecidableEq D]

/-- An injection between finite subsets, including empty subsets. -/
theorem subset_embedding (A B : Finset V) (h : A.card ≤ B.card) :
    ∃ f : A → B, Function.Injective f := by
  classical
  obtain ⟨g, hg⟩ := embed_palette A B.card h
  let e : Fin B.card ≃ B := Fintype.equivOfCardEq (by simp)
  exact ⟨fun a => e (g a), e.injective.comp hg⟩

/-- Label each neighborhood injectively inside the larger one, fixing its vertices. -/
theorem common_labels (S T : Finset V) (hst : S.card ≤ T.card) (ht : T.Nonempty) :
    ∃ r : V → T, Set.InjOn r S ∧ Set.InjOn r T := by
  classical
  obtain ⟨g, hg⟩ := subset_embedding (S \ T) (T \ S) (card_sdiff_le_card_sdiff_iff.mpr hst)
  obtain ⟨w, hw⟩ := ht
  let r : V → T := fun v => if hv : v ∈ T then ⟨v, hv⟩
    else if hs : v ∈ S then ⟨(g ⟨v, mem_sdiff.mpr ⟨hs, hv⟩⟩).val,
      (mem_sdiff.mp (g ⟨v, mem_sdiff.mpr ⟨hs, hv⟩⟩).property).1⟩ else ⟨w, hw⟩
  have fixed (v) (hv : v ∈ T) : (r v).val = v := by simp [r, hv]
  have moved (v) (hv : v ∈ S) (hn : v ∉ T) :
      (r v).val = (g ⟨v, mem_sdiff.mpr ⟨hv, hn⟩⟩).val := by simp [r, hn, hv]
  refine ⟨r, ?_, ?_⟩
  · intro v hv u hu he
    have hh := congrArg Subtype.val he
    by_cases hvt : v ∈ T <;> by_cases hut : u ∈ T
    · simpa only [fixed v hvt, fixed u hut] using hh
    · rw [fixed v hvt, moved u hu hut] at hh
      exact False.elim ((mem_sdiff.mp (g ⟨u, mem_sdiff.mpr ⟨hu, hut⟩⟩).property).2 (hh ▸ hv))
    · rw [moved v hv hvt, fixed u hut] at hh
      exact False.elim ((mem_sdiff.mp (g ⟨v, mem_sdiff.mpr ⟨hv, hvt⟩⟩).property).2 (hh.symm ▸ hu))
    · rw [moved v hv hvt, moved u hu hut] at hh
      exact congrArg Subtype.val (hg (Subtype.ext hh))
  · intro v hv u hu he
    have hh := congrArg Subtype.val he
    simpa only [fixed v hv, fixed u hu] using hh

/-- Pull back proper edge colors along a map injective on one neighborhood. -/
theorem pullback_proper {W K : Type*} [DecidableEq W] [Nonempty K]
    (S : Finset V) (r : V → W) (hr : Set.InjOn r S) (f : PairColoring W K) :
    ProperOn S (fun e => f.edgeColor (e.image r)) := by
  classical
  intro e he d hd v hve hvd hc
  have heS := (mem_powersetCard.mp he).1
  have hdS := (mem_powersetCard.mp hd).1
  have hec : (e.image r).card = 2 := by
    rw [card_image_of_injOn (fun a ha b hb hh => hr (heS ha) (heS hb) hh)]
    exact (mem_powersetCard.mp he).2
  have hdc : (d.image r).card = 2 := by
    rw [card_image_of_injOn (fun a ha b hb hh => hr (hdS ha) (hdS hb) hh)]
    exact (mem_powersetCard.mp hd).2
  have hi := f.edgeColor_proper hec hdc (mem_image.mpr ⟨v, hve, rfl⟩)
    (mem_image.mpr ⟨v, hvd, rfl⟩) hc
  ext a
  constructor
  · intro ha
    have hmem : r a ∈ d.image r := hi ▸ (mem_image.mpr ⟨a, ha, rfl⟩)
    obtain ⟨b, hb, hh⟩ := mem_image.mp hmem
    have : b = a := hr (hdS hb) (heS ha) hh
    simpa [this] using hb
  · intro ha
    have hmem : r a ∈ e.image r := hi.symm ▸ (mem_image.mpr ⟨a, ha, rfl⟩)
    obtain ⟨b, hb, hh⟩ := mem_image.mp hmem
    have : b = a := hr (heS hb) (hdS ha) hh
    simpa [this] using hb

theorem coherent_coloring_ordered (S T : Finset V) (ht : 2 ≤ T.card) (hst : S.card ≤ T.card) :
    ∃ f : Finset V → Fin (colorCount T.card), ProperOn S f ∧ ProperOn T f := by
  classical
  obtain ⟨r, hrs, hrt⟩ := common_labels S T hst (card_pos.mp (by omega))
  have ht' : 2 ≤ Fintype.card T := by simpa using ht
  have hp : 0 < colorCount (Fintype.card T) := by unfold colorCount; split <;> omega
  letI : NeZero (colorCount (Fintype.card T)) := ⟨by omega⟩
  obtain ⟨g⟩ := complete_graph_coloring (V := T) ht'
  let e : Fin (colorCount (Fintype.card T)) ≃ Fin (colorCount T.card) :=
    Fintype.equivOfCardEq (by simp)
  let f : Finset V → Fin (colorCount T.card) := fun a => e (g.edgeColor (a.image r))
  refine ⟨f, ?_, ?_⟩
  · intro a ha b hb v hva hvb hh
    exact pullback_proper S r hrs g a ha b hb v hva hvb (e.injective hh)
  · intro a ha b hb v hva hvb hh
    exact pullback_proper T r hrt g a ha b hb v hva hvb (e.injective hh)

/-- One color function is proper separately on S and T; shared edges agree automatically. -/
theorem coherent_coloring (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card) :
    ∃ f : Finset V → Fin (colorCount (max S.card T.card)), ProperOn S f ∧ ProperOn T f := by
  by_cases h : S.card ≤ T.card
  · rw [max_eq_right h]
    exact coherent_coloring_ordered S T ht h
  · have h' : T.card ≤ S.card := by omega
    rw [max_eq_left h']
    obtain ⟨f, hf, hg⟩ := coherent_coloring_ordered T S hs h'
    exact ⟨f, hg, hf⟩

/-- Two palettes can have the smallest intersection permitted by their sizes. -/
theorem minimal_palettes [Fintype C] (p q : ℕ)
    (hp : p ≤ Fintype.card C) (hq : q ≤ Fintype.card C) :
    ∃ A B : Finset C, A.card = p ∧ B.card = q ∧
      (A ∩ B).card = p + q - Fintype.card C := by
  classical
  obtain ⟨A, _, hA⟩ := exists_subset_card_eq (s := (univ : Finset C)) (by simpa using hp)
  let R := (univ : Finset C) \ A
  have hR : R.card + p = Fintype.card C := by
    have := card_sdiff_add_card_eq_card (subset_univ A)
    simpa only [R, hA, card_univ] using this
  by_cases hqR : q ≤ R.card
  · obtain ⟨B, hBR, hB⟩ := exists_subset_card_eq hqR
    have hi : A ∩ B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro c hc
      exact (mem_sdiff.mp (hBR (mem_inter.mp hc).2)).2 (mem_inter.mp hc).1
    refine ⟨A, B, hA, hB, ?_⟩
    rw [hi, card_empty]
    omega
  · obtain ⟨B, hRB, _, hB⟩ := exists_subsuperset_card_eq
      (subset_univ R) (show R.card ≤ q by omega) (by simpa using hq)
    have hu : A ∪ B = univ := by
      apply eq_univ_iff_forall.mpr
      intro c
      by_cases hc : c ∈ A
      · exact mem_union_left _ hc
      · exact mem_union_right _ (hRB (mem_sdiff.mpr ⟨mem_univ _, hc⟩))
    have hi := card_union_add_card_inter A B
    rw [hu, card_univ, hA, hB] at hi
    exact ⟨A, B, hA, hB, by omega⟩

section Shifts
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def shift (A : Finset G) (k : G) : Finset G := univ.filter (fun c => c + k ∈ A)

theorem shift_card (A : Finset G) (k : G) : (shift A k).card = A.card := by
  have hi : shift A k = A.image (fun c => c - k) := by
    ext c
    simp only [shift, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hc
      exact ⟨c+k, hc, add_sub_cancel_right c k⟩
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
  rw [hi]
  apply card_image_of_injective
  intro a b hh
  have he := congrArg (fun x : G => x + k) hh
  simpa only [sub_add_cancel] using he

theorem shift_inter (A B : Finset G) (k : G) : shift A k ∩ shift B k = shift (A ∩ B) k := by
  ext c
  simp [shift, and_assoc]

/-- Every color belongs to exactly |A| of the translated palettes. -/
theorem shift_frequency (A : Finset G) (c : G) :
    ((univ : Finset G).filter (fun k => c + k ∈ A)).card = A.card := by
  simpa only [shift, add_comm] using shift_card A c

/-- Count chosen edges over all translations, using a finite double sum. -/
theorem shift_total {α : Type*} [DecidableEq α] (E : Finset α) (f : α → G) (A : Finset G) :
    (∑ k : G, (E.filter (fun e => f e ∈ shift A k)).card) = A.card * E.card := by
  calc
    (∑ k : G, (E.filter (fun e => f e ∈ shift A k)).card) =
        ∑ e ∈ E, ((univ : Finset G).filter (fun k => f e + k ∈ A)).card := by
      simp only [card_eq_sum_ones, sum_filter, shift, mem_filter, mem_univ, true_and]
      rw [sum_comm]
    _ = ∑ _e ∈ E, A.card := sum_congr rfl (fun e he => shift_frequency A (f e))
    _ = A.card * E.card := by simp [mul_comm]

/-- Some common translation attains the controlled-overlap union bound. -/
theorem select_coupled {α : Type*} [DecidableEq α] (E F : Finset α) (f : α → G)
    (p q : ℕ) (hp : p ≤ Fintype.card G) (hq : q ≤ Fintype.card G) :
    ∃ A B : Finset G, A.card = p ∧ B.card = q ∧
      p * E.card + q * F.card ≤ Fintype.card G *
        ((E.filter (fun e => f e ∈ A)) ∪ (F.filter (fun e => f e ∈ B))).card +
        (p + q - Fintype.card G) * (E ∩ F).card := by
  classical
  obtain ⟨A, B, hA, hB, hAB⟩ := minimal_palettes (C := G) p q hp hq
  let J := fun k => E.filter (fun e => f e ∈ shift A k)
  let K := fun k => F.filter (fun e => f e ∈ shift B k)
  let U := fun k => (J k ∪ K k).card
  have hinter (k : G) : J k ∩ K k = (E ∩ F).filter (fun e => f e ∈ shift (A ∩ B) k) := by
    ext e
    simp only [J, K, mem_inter, mem_filter, shift, mem_univ, true_and]
    tauto
  have hsum : (∑ k : G, U k) + (p+q-Fintype.card G) * (E ∩ F).card = p*E.card + q*F.card := by
    have hc : (∑ k : G, (J k ∪ K k).card) + (∑ k : G, (J k ∩ K k).card) =
        (∑ k : G, (J k).card) + ∑ k : G, (K k).card := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl (fun k _ => card_union_add_card_inter (J k) (K k))
    have hI : (∑ k : G, (J k ∩ K k).card) = (p+q-Fintype.card G)*(E ∩ F).card := by
      simp_rw [hinter]
      rw [shift_total, hAB]
    have hJ : (∑ k : G, (J k).card) = p*E.card := by dsimp only [J]; rw [shift_total, hA]
    have hK : (∑ k : G, (K k).card) = q*F.card := by dsimp only [K]; rw [shift_total, hB]
    simpa only [hI, hJ, hK] using hc
  obtain ⟨k, _, hmax⟩ := exists_max_image (univ : Finset G) U (by simp)
  have hb : (∑ j : G, U j) ≤ Fintype.card G * U k := by
    calc
      (∑ j : G, U j) ≤ ∑ _j : G, U k := sum_le_sum (fun j hj => hmax j hj)
      _ = Fintype.card G * U k := by simp
  refine ⟨shift A k, shift B k, (shift_card A k).trans hA, (shift_card B k).trans hB, ?_⟩
  change p*E.card + q*F.card ≤ Fintype.card G * U k + _
  rw [← hsum]
  exact Nat.add_le_add_right hb _
end Shifts

/-- Merge two colored edge sets, giving each shared edge to the first type exactly once. -/
theorem merge_general [DecidableEq X] [DecidableEq Y] [Nonempty (C ⊕ D)] (H : SimpleGraph V) (S T : Finset V)
    (hS : H.IsClique S) (hT : H.IsClique T)
    (f : Finset V → X) (g : Finset V → Y)
    (hf : ProperOn S f) (hg : ProperOn T g)
    (A : Finset (X)) (B : Finset (Y))
    (ca : A → C) (cb : B → D) (hca : Function.Injective ca) (hcb : Function.Injective cb) :
    ∃ P : Finset (Finset (V ⊕ (C ⊕ D))), IsPacking (twoAttached H S T C D) P ∧
      P.card = (selectedEdges S f A ∪ selectedEdges T g B).card ∧
      ∀ t ∈ P, t.toRight.Nonempty := by
  classical
  let J := selectedEdges S f A
  let K := selectedEdges T g B
  let chosen : Finset V → C ⊕ D := fun e =>
    if he : e ∈ J then Sum.inl (ca ⟨f e, (mem_filter.mp he).2⟩)
    else if he : e ∈ K then Sum.inr (cb ⟨g e, (mem_filter.mp he).2⟩)
    else Classical.choice ‹Nonempty (C ⊕ D)›
  have hleft (e) (he : e ∈ J) : chosen e = Sum.inl (ca ⟨f e, (mem_filter.mp he).2⟩) := by
    simp [chosen, he]
  have hright (e) (he : e ∉ J) (hk : e ∈ K) : chosen e = Sum.inr (cb ⟨g e, (mem_filter.mp hk).2⟩) := by
    simp [chosen, he, hk]
  have hproper : ∀ e ∈ J ∪ K, ∀ d ∈ J ∪ K, ∀ v ∈ e, v ∈ d → chosen e = chosen d → e = d := by
    intro e he d hd v hve hvd hc
    by_cases heJ : e ∈ J <;> by_cases hdJ : d ∈ J
    · rw [hleft e heJ, hleft d hdJ] at hc
      exact hf e (mem_filter.mp heJ).1 d (mem_filter.mp hdJ).1 v hve hvd
        (congrArg Subtype.val (hca (Sum.inl.inj hc)))
    · have hdK := (mem_union.mp hd).resolve_left hdJ
      rw [hleft e heJ, hright d hdJ hdK] at hc
      cases hc
    · have heK := (mem_union.mp he).resolve_left heJ
      rw [hright e heJ heK, hleft d hdJ] at hc
      cases hc
    · have heK := (mem_union.mp he).resolve_left heJ
      have hdK := (mem_union.mp hd).resolve_left hdJ
      rw [hright e heJ heK, hright d hdJ hdK] at hc
      exact hg e (mem_filter.mp heK).1 d (mem_filter.mp hdK).1 v hve hvd
        (congrArg Subtype.val (hcb (Sum.inr.inj hc)))
  have hcard : ∀ e ∈ J ∪ K, e.card = 2 := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact (mem_powersetCard.mp (mem_filter.mp he).1).2
    · exact (mem_powersetCard.mp (mem_filter.mp he).1).2
  refine ⟨(J ∪ K).image (cone chosen), ⟨?_, cones_edge_disjoint _ hcard chosen hproper⟩,
    card_image_of_injective _ (cone_injective chosen), ?_⟩
  · intro t ht
    obtain ⟨e, he, rfl⟩ := mem_image.mp ht
    by_cases heJ : e ∈ J
    · have heS := (mem_powersetCard.mp (mem_filter.mp heJ).1).1
      have heH : H.IsNClique 2 e := ⟨by
        intro a ha b hb hne
        exact hS (heS ha) (heS hb) hne, hcard e he⟩
      apply cone_two_triangle heH chosen
      rw [hleft e heJ]
      exact heS
    · have heK := (mem_union.mp he).resolve_left heJ
      have heT := (mem_powersetCard.mp (mem_filter.mp heK).1).1
      have heH : H.IsNClique 2 e := ⟨by
        intro a ha b hb hne
        exact hT (heT ha) (heT hb) hne, hcard e he⟩
      apply cone_two_triangle heH chosen
      rw [hright e heJ heK]
      exact heT
  · intro t ht
    obtain ⟨e, he, rfl⟩ := mem_image.mp ht
    exact ⟨chosen e, mem_toRight.mpr (by simp)⟩


/-- The coupled-color bound as an actual centered graph packing, for all sizes. -/
theorem coupled_allocation (H : SimpleGraph V) (S T : Finset V)
    (hs : 2 ≤ S.card) (ht : 2 ≤ T.card) (hS : H.IsClique S) (hT : H.IsClique T) (m n : ℕ) :
    ∃ P : Finset (Finset (V ⊕ (Fin m ⊕ Fin n))),
      IsPacking (twoAttached H S T (Fin m) (Fin n)) P ∧
      min m (colorCount (max S.card T.card)) * S.card.choose 2 +
        min n (colorCount (max S.card T.card)) * T.card.choose 2 ≤
      colorCount (max S.card T.card) * P.card +
        (min m (colorCount (max S.card T.card)) + min n (colorCount (max S.card T.card)) -
          colorCount (max S.card T.card)) * (S ∩ T).card.choose 2 ∧
      ∀ t ∈ P, t.toRight.Nonempty := by
  classical
  by_cases hz : m = 0 ∧ n = 0
  · rcases hz with ⟨rfl, rfl⟩
    exact ⟨∅, by simp [IsPacking], by simp, by simp⟩
  · letI : Nonempty (Fin m ⊕ Fin n) := by
      by_cases hm : m = 0
      · exact ⟨Sum.inr ⟨0, by omega⟩⟩
      · exact ⟨Sum.inl ⟨0, by omega⟩⟩
    let h := colorCount (max S.card T.card)
    have hd : 2 ≤ max S.card T.card := hs.trans (le_max_left _ _)
    have hh : 0 < h := by dsimp only [h]; unfold colorCount; split <;> omega
    letI : NeZero h := ⟨by omega⟩
    obtain ⟨f, hf, hg⟩ := coherent_coloring S T hs ht
    let ec : Fin h ≃ ZMod h := Fintype.equivOfCardEq (by simp)
    let color : Finset V → ZMod h := fun e => ec (f e)
    have hproperS : ProperOn S color := by
      intro e he d hd v hve hvd hc
      exact hf e he d hd v hve hvd (ec.injective hc)
    have hproperT : ProperOn T color := by
      intro e he d hd v hve hvd hc
      exact hg e he d hd v hve hvd (ec.injective hc)
    obtain ⟨A, B, hA, hB, hb⟩ := select_coupled (S.powersetCard 2) (T.powersetCard 2)
      color (min m h) (min n h) (by simpa using Nat.min_le_right m h)
      (by simpa using Nat.min_le_right n h)
    obtain ⟨ca, hca⟩ := embed_palette A m (by rw [hA]; exact Nat.min_le_left _ _)
    obtain ⟨cb, hcb⟩ := embed_palette B n (by rw [hB]; exact Nat.min_le_left _ _)
    obtain ⟨P, hP, hPc, hout⟩ := merge_general H S T hS hT color color hproperS hproperT
      A B ca cb hca hcb
    refine ⟨P, hP, ?_, hout⟩
    rw [hPc]
    simpa [h, selectedEdges, common_edges] using hb

/-- The same integer inequality for the attained finite-graph packing optimum. -/
theorem coupled_allocation_bound [Fintype V] (H : SimpleGraph V) (S T : Finset V)
    (hs : 2 ≤ S.card) (ht : 2 ≤ T.card) (hS : H.IsClique S) (hT : H.IsClique T) (m n : ℕ) :
      min m (colorCount (max S.card T.card)) * S.card.choose 2 +
        min n (colorCount (max S.card T.card)) * T.card.choose 2 ≤
      colorCount (max S.card T.card) * packingNumber (twoAttached H S T (Fin m) (Fin n)) +
        (min m (colorCount (max S.card T.card)) + min n (colorCount (max S.card T.card)) -
          colorCount (max S.card T.card)) * (S ∩ T).card.choose 2 := by
  obtain ⟨P, hP, hb, _⟩ := coupled_allocation H S T hs ht hS hT m n
  obtain ⟨Q, hQ, hQc, hmax⟩ := packingNumber_spec (twoAttached H S T (Fin m) (Fin n))
  exact hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (hmax P hP)) _)

#print axioms common_labels
#print axioms coherent_coloring
#print axioms minimal_palettes
#print axioms shift_total
#print axioms select_coupled
#print axioms merge_general
#print axioms coupled_allocation
#print axioms coupled_allocation_bound
#check coupled_allocation_bound
end TuzaCoupledAllocation


/-! Greedy completion in a complete core, preserving the input packing.
OpenAI Codex (GPT-6 Astra), 2026-10-07. -/
namespace TuzaCoreCompletion
open Finset TuzaCompression TuzaGraphCompression TuzaMatchingClasses
  TuzaIndependentAllocation TuzaCoupledAllocation
variable {V C : Type*} [DecidableEq V] [DecidableEq C]

/-- A graph represented by its finite family of two-element edges. -/
def familyGraph (E : Finset (Finset V)) : SimpleGraph V where
  Adj a b := a ≠ b ∧ {a,b} ∈ E
  symm.symm a b h := ⟨h.1.symm, by simpa only [pair_comm] using h.2⟩
  loopless.irrefl a h := h.1 rfl

/-- Translate a triangle clique into its three actual core edges. -/
theorem family_triangle (E : Finset (Finset V)) (t : Finset V) :
    (familyGraph E).IsNClique 3 t ↔ t.card = 3 ∧ t.powersetCard 2 ⊆ E := by
  constructor
  · intro ht
    refine ⟨ht.card_eq, ?_⟩
    intro e he
    obtain ⟨hes, hec⟩ := mem_powersetCard.mp he
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hec
    exact (ht.isClique (hes (by simp)) (hes (by simp)) hab).2
  · rintro ⟨hc, he⟩
    refine ⟨?_, hc⟩
    intro a ha b hb hab
    exact ⟨hab, he (mem_powersetCard.mpr ⟨by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption, card_pair hab⟩)⟩

/-- Mantel from the pinned Mathlib Turan theorem, in our edge representation. -/
theorem mantel_family [Fintype V] (E : Finset (Finset V))
    (hE : ∀ e ∈ E, e.card = 2) (htf : (familyGraph E).CliqueFree 3) :
    E.card ≤ (Fintype.card V)^2 / 4 := by
  classical
  let G := familyGraph E
  have himage : G.edgeFinset.image Sym2.toFinset = E := by
    ext e
    constructor
    · intro he
      obtain ⟨q, hq, rfl⟩ := mem_image.mp he
      induction q using Sym2.inductionOn with
      | hf a b =>
        have h : G.Adj a b := by simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hq
        simpa only [Sym2.toFinset_mk_eq] using h.2
    · intro he
      obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp (hE e he)
      refine mem_image.mpr ⟨s(a,b), ?_, Sym2.toFinset_mk_eq⟩
      change s(a,b) ∈ G.edgeFinset
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using (show G.Adj a b from ⟨hab,he⟩)
  have hcard : E.card ≤ G.edgeFinset.card := by
    rw [← himage]
    exact card_image_le
  have ht : G.edgeFinset.card ≤ (Fintype.card V)^2 / 4 := by
    simpa only [SimpleGraph.turanNumber_two] using
      (SimpleGraph.CliqueFree.card_edgeFinset_le (r := 2) htf)
  exact hcard.trans ht

def usedEdges (Q : Finset (Finset V)) : Finset (Finset V) :=
  Q.biUnion (fun t => t.powersetCard 2)

theorem used_edges_card {G : SimpleGraph V} {Q : Finset (Finset V)} (hQ : IsPacking G Q) :
    (usedEdges Q).card = 3 * Q.card := by
  rw [usedEdges, card_biUnion hQ.2]
  calc
    (∑ t ∈ Q, (t.powersetCard 2).card) = ∑ _t ∈ Q, 3 := by
      apply sum_congr rfl
      intro t ht
      rw [card_powersetCard, (hQ.1 t ht).card_eq]
      decide
    _ = 3*Q.card := by simp [mul_comm]

theorem used_edges_subset {E : Finset (Finset V)} {Q : Finset (Finset V)}
    (hQ : IsPacking (familyGraph E) Q) : usedEdges Q ⊆ E := by
  intro e he
  obtain ⟨t,ht,het⟩ := mem_biUnion.mp he
  exact (family_triangle E t |>.mp (hQ.1 t ht)).2 het

/-- Add a triangle avoiding every already used edge. -/
theorem insert_packing {G : SimpleGraph V} {Q : Finset (Finset V)} {t : Finset V}
    (hQ : IsPacking G Q) (ht : G.IsNClique 3 t)
    (havoid : Disjoint (t.powersetCard 2) (usedEdges Q)) :
    IsPacking G (insert t Q) ∧ t ∉ Q := by
  have hn : t ∉ Q := by
    intro hmem
    have he : (t.powersetCard 2).Nonempty := card_pos.mp (by
      rw [card_powersetCard, ht.card_eq]; decide)
    obtain ⟨e,he⟩ := he
    exact disjoint_left.mp havoid he (mem_biUnion.mpr ⟨t,hmem,he⟩)
  have hx (q) (hq : q ∈ Q) : Disjoint (t.powersetCard 2) (q.powersetCard 2) := by
    apply disjoint_left.mpr
    intro e he heq
    exact disjoint_left.mp havoid he (mem_biUnion.mpr ⟨q,hq,heq⟩)
  refine ⟨⟨?_, ?_⟩,hn⟩
  · intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact ht
    · exact hQ.1 q hq
  · intro a ha b hb hne
    by_cases hat : a = t
    · subst a
      have hbQ : b ∈ Q := (mem_insert.mp hb).resolve_left hne.symm
      exact hx b hbQ
    · have haQ : a ∈ Q := (mem_insert.mp ha).resolve_left hat
      by_cases hbt : b = t
      · subst b
        exact (hx a haQ).symm
      · have hbQ : b ∈ Q := (mem_insert.mp hb).resolve_left hbt
        exact hQ.2 haQ hbQ hne

/-- A maximal triangle packing leaves a triangle-free residual edge family. -/
theorem residual_triangle_free {E : Finset (Finset V)} {Q : Finset (Finset V)}
    (hQ : IsPacking (familyGraph E) Q)
    (hmax : ∀ R, IsPacking (familyGraph E) R → R.card ≤ Q.card) :
    (familyGraph (E \ usedEdges Q)).CliqueFree 3 := by
  intro t ht
  have htc := family_triangle _ _ |>.mp ht
  have htE : (familyGraph E).IsNClique 3 t := family_triangle _ _ |>.mpr
    ⟨htc.1, fun e he => (mem_sdiff.mp (htc.2 he)).1⟩
  have hd : Disjoint (t.powersetCard 2) (usedEdges Q) := by
    apply disjoint_left.mpr
    intro e he hu
    exact (mem_sdiff.mp (htc.2 he)).2 hu
  obtain ⟨hins,hn⟩ := insert_packing hQ htE hd
  have hh := hmax (insert t Q) hins
  rw [card_insert_of_notMem hn] at hh
  omega

/-- An arbitrary finite core-edge family has a large maximal triangle packing. -/
theorem residual_packing [Fintype V] (E : Finset (Finset V)) (hE : ∀ e ∈ E, e.card = 2) :
    ∃ Q : Finset (Finset V), IsPacking (familyGraph E) Q ∧
      E.card ≤ 3*Q.card + (Fintype.card V)^2 / 4 := by
  classical
  obtain ⟨Q,hQ,hQc,hmax⟩ := packingNumber_spec (familyGraph E)
  have hm : ∀ R, IsPacking (familyGraph E) R → R.card ≤ Q.card := by
    intro R hR
    rw [hQc]
    exact hmax R hR
  have hb := mantel_family (E \ usedEdges Q)
    (fun e he => hE e (mem_sdiff.mp he).1) (residual_triangle_free hQ hm)
  have hc := card_sdiff_add_card_eq_card (used_edges_subset hQ)
  rw [used_edges_card hQ] at hc
  exact ⟨Q,hQ,by omega⟩

/-- Independence of the outer vertices leaves exactly one core edge per centered triangle. -/
theorem centered_left_card (G : SimpleGraph (V ⊕ C))
    (hind : ∀ c d, ¬G.Adj (Sum.inr c) (Sum.inr d))
    {t : Finset (V ⊕ C)} (ht : G.IsNClique 3 t) (hout : t.toRight.Nonempty) :
    t.toLeft.card = 2 := by
  have hr : t.toRight.card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    by_contra hab
    exact hind a b (ht.isClique (mem_toRight.mp ha) (mem_toRight.mp hb)
      (fun h => hab (Sum.inr.inj h)))
  have hp := card_pos.mpr hout
  have hc := card_toLeft_add_card_toRight (u := t)
  have htcard := ht.card_eq
  omega

/-- Distinct packed triangles cannot use the same two-element core edge. -/
theorem core_collision_general {G : SimpleGraph (V ⊕ C)}
    {P : Finset (Finset (V ⊕ C))} (hP : IsPacking G P)
    {t u : Finset (V ⊕ C)} (ht : t ∈ P) (hu : u ∈ P)
    {e : Finset V} (he : e.card = 2) (het : e ⊆ t.toLeft) (heu : e ⊆ u.toLeft) : t = u := by
  by_contra hne
  have hec : (lift (C := C) e).card = 2 := by simpa using he
  exact disjoint_left.mp (hP.2 ht hu hne)
    (mem_powersetCard.mpr ⟨lift_subset_of_left het, hec⟩)
    (mem_powersetCard.mpr ⟨lift_subset_of_left heu, hec⟩)

/-- A centered triangle avoids every lifted triangle that avoids its core edge. -/
theorem left_lift_disjoint {t : Finset (V ⊕ C)} {q : Finset V}
    (ht : t.toLeft.card = 2) (havoid : ¬t.toLeft ⊆ q) :
    Disjoint (t.powersetCard 2) ((lift (C := C) q).powersetCard 2) := by
  apply disjoint_left.mpr
  intro e het heq
  obtain ⟨hets,hec⟩ := mem_powersetCard.mp het
  obtain ⟨heqs,_⟩ := mem_powersetCard.mp heq
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hec
  have hat := hets (by simp : a ∈ ({a,b} : Finset (V ⊕ C)))
  have hbt := hets (by simp : b ∈ ({a,b} : Finset (V ⊕ C)))
  have haq := heqs (by simp : a ∈ ({a,b} : Finset (V ⊕ C)))
  have hbq := heqs (by simp : b ∈ ({a,b} : Finset (V ⊕ C)))
  cases a with
  | inr a => exact inr_not_mem_lift haq
  | inl a =>
    cases b with
    | inr b => exact inr_not_mem_lift hbq
    | inl b =>
      have heq := edge_subset_eq (fun h => hab (congrArg Sum.inl h)) ht
        (mem_toLeft.mpr hat) (mem_toLeft.mpr hbt)
      apply havoid
      rw [← heq]
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact inl_mem_lift.mp haq
      · exact inl_mem_lift.mp hbq

/-- Preserve any given centered packing and add triangles from the unused complete core.
No restriction on the number of outer-neighborhood types is imposed. -/
theorem core_completion [Fintype V] (G : SimpleGraph (V ⊕ C))
    (hcore : ∀ a b : V, a ≠ b → G.Adj (Sum.inl a) (Sum.inl b))
    (hind : ∀ c d : C, ¬G.Adj (Sum.inr c) (Sum.inr d))
    (P : Finset (Finset (V ⊕ C))) (hP : IsPacking G P)
    (hout : ∀ t ∈ P, t.toRight.Nonempty) :
    ∃ R : Finset (Finset (V ⊕ C)), IsPacking G R ∧ P ⊆ R ∧
      2*P.card + (Fintype.card V).choose 2 ≤ 3*R.card + (Fintype.card V)^2 / 4 := by
  classical
  let J := P.image Finset.toLeft
  have hleft (t) (ht : t ∈ P) : t.toLeft.card = 2 := centered_left_card G hind (hP.1 t ht) (hout t ht)
  have hJcard : J.card = P.card := by
    apply card_image_of_injOn
    intro t ht u hu htu
    exact core_collision_general hP ht hu (hleft t ht) (Subset.refl _) (by rw [htu])
  have hJ : ∀ e ∈ J, e.card = 2 := by
    intro e he
    obtain ⟨t,ht,rfl⟩ := mem_image.mp he
    exact hleft t ht
  let All := (univ : Finset V).powersetCard 2
  let E := All \ J
  have hJA : J ⊆ All := fun e he => mem_powersetCard.mpr ⟨subset_univ _,hJ e he⟩
  have hE : ∀ e ∈ E, e.card = 2 := fun e he => (mem_powersetCard.mp (mem_sdiff.mp he).1).2
  have hEc : E.card + P.card = (Fintype.card V).choose 2 := by
    have hc := card_sdiff_add_card_eq_card hJA
    simpa only [hJcard, All, card_powersetCard, card_univ] using hc
  obtain ⟨Q,hQ,hbound⟩ := residual_packing E hE
  let L := Q.image (lift (C := C))
  have hL : IsPacking G L := by
    refine ⟨?_, lift_packing Q hQ.2⟩
    intro t ht
    obtain ⟨q,hq,rfl⟩ := mem_image.mp ht
    refine ⟨?_, by rw [lift_card, (hQ.1 q hq).card_eq]⟩
    intro a ha b hb hab
    obtain ⟨v,hv,rfl⟩ := mem_image.mp ha
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hb
    exact hcore v w (fun h => hab (congrArg Sum.inl h))
  have hcross : ∀ t ∈ P, ∀ u ∈ L, Disjoint (t.powersetCard 2) (u.powersetCard 2) := by
    intro t ht u hu
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hu
    apply left_lift_disjoint (hleft t ht)
    intro hsub
    have he : t.toLeft ∈ E := (family_triangle E q |>.mp (hQ.1 q hq)).2
      (mem_powersetCard.mpr ⟨hsub,hleft t ht⟩)
    exact (mem_sdiff.mp he).2 (mem_image.mpr ⟨t,ht,rfl⟩)
  have hdis : Disjoint P L := by
    apply disjoint_left.mpr
    intro t ht hu
    obtain ⟨q,hq,heq⟩ := mem_image.mp hu
    obtain ⟨c,hc⟩ := hout t ht
    have hm := mem_toRight.mp hc
    rw [← heq] at hm
    exact inr_not_mem_lift hm
  have hLc : L.card = Q.card := card_image_of_injective Q lift_injective
  have hRc : (P ∪ L).card = P.card + Q.card := by rw [card_union_of_disjoint hdis, hLc]
  refine ⟨P ∪ L, ⟨?_, ?_⟩, subset_union_left, ?_⟩
  · intro t ht
    rcases mem_union.mp ht with ht | ht
    · exact hP.1 t ht
    · exact hL.1 t ht
  · intro t ht u hu hne
    rcases mem_union.mp ht with ht | ht <;> rcases mem_union.mp hu with hu | hu
    · exact hP.2 ht hu hne
    · exact hcross t ht u hu
    · exact (hcross u hu t ht).symm
    · exact hL.2 ht hu hne
  · rw [hRc]
    omega

/-- Completion also bounds the attained optimum for every finite split graph presentation. -/
theorem core_completion_bound [Fintype V] [Fintype C] (G : SimpleGraph (V ⊕ C))
    (hcore : ∀ a b : V, a ≠ b → G.Adj (Sum.inl a) (Sum.inl b))
    (hind : ∀ c d : C, ¬G.Adj (Sum.inr c) (Sum.inr d))
    (P : Finset (Finset (V ⊕ C))) (hP : IsPacking G P)
    (hout : ∀ t ∈ P, t.toRight.Nonempty) :
    P.card ≤ packingNumber G ∧
      2*P.card + (Fintype.card V).choose 2 ≤ 3*packingNumber G + (Fintype.card V)^2 / 4 := by
  obtain ⟨R,hR,hsub,hb⟩ := core_completion G hcore hind P hP hout
  obtain ⟨M,hM,hMc,hmax⟩ := packingNumber_spec G
  exact ⟨hmax P hP, hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (hmax R hR)) _)⟩

/-- Explicit bridge to the two-neighborhood graph used by both verified allocation bounds. -/
theorem two_type_completion [Fintype V] (S T : Finset V) (m n : ℕ)
    (P : Finset (Finset (V ⊕ (Fin m ⊕ Fin n))))
    (hP : IsPacking (twoAttached (⊤ : SimpleGraph V) S T (Fin m) (Fin n)) P)
    (hout : ∀ t ∈ P, t.toRight.Nonempty) :
    ∃ R : Finset (Finset (V ⊕ (Fin m ⊕ Fin n))),
      IsPacking (twoAttached (⊤ : SimpleGraph V) S T (Fin m) (Fin n)) R ∧ P ⊆ R ∧
      2*P.card + (Fintype.card V).choose 2 ≤ 3*R.card + (Fintype.card V)^2 / 4 := by
  apply core_completion _ ?_ ?_ P hP hout
  · intro a b hab
    exact hab
  · intro c d h
    exact h

#print axioms mantel_family
#print axioms residual_triangle_free
#print axioms residual_packing
#print axioms centered_left_card
#print axioms core_completion
#print axioms core_completion_bound
#print axioms two_type_completion
#check core_completion
end TuzaCoreCompletion


namespace TuzaCoverCompression
open Finset TuzaCompression TuzaGraphCompression

variable {V W C D : Type*} [DecidableEq V] [DecidableEq W]
  [DecidableEq C] [DecidableEq D]

def IsCover (H : SimpleGraph V) (F : Finset (Finset V)) : Prop :=
  (∀ e ∈ F, H.IsNClique 2 e) ∧
  (∀ t : Finset V, H.IsNClique 3 t → ∃ e ∈ F, e ⊆ t)

def spoke (c : C) (v : V) : Finset (V ⊕ C) := {Sum.inl v, Sum.inr c}

@[simp] theorem spoke_left (c : C) (v : V) : (spoke c v).toLeft = {v} := by
  ext x
  simp [spoke]
@[simp] theorem spoke_right (c : C) (v : V) : (spoke c v).toRight = {c} := by
  ext x
  simp [spoke]
@[simp] theorem lift_left (e : Finset V) : (lift (C := C) e).toLeft = e := by
  ext x
  simp
@[simp] theorem lift_right (e : Finset V) : (lift (C := C) e).toRight = ∅ := by
  ext x
  simp

theorem spoke_injective (c : C) : Function.Injective (spoke (V := V) c) := by
  intro a b h
  have hh := congrArg Finset.toLeft h
  simpa using hh

theorem spoke_center_eq {c d : C} {v w : V} (h : spoke c v = spoke d w) : c = d := by
  have hh := congrArg Finset.toRight h
  simpa using hh

theorem edge_other {e : Finset V} (he : e.card = 2) {v : V} (hv : v ∈ e) :
    ∃ w, v ≠ w ∧ e = {v, w} := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp he
  simp only [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact ⟨b, hab, rfl⟩
  · exact ⟨a, hab.symm, pair_comm _ _⟩

/-- A vertex cover of edges inside S accounts for at most |S|-1 edges per selected vertex. -/
theorem edge_cover_cost (S Z : Finset V) (J : Finset (Finset V))
    (hZ : Z ⊆ S) (hJ : ∀ e ∈ J, e.card = 2) (hJS : ∀ e ∈ J, e ⊆ S)
    (hhit : ∀ e ∈ J, ∃ v ∈ Z, v ∈ e) : J.card ≤ (S.card - 1) * Z.card := by
  classical
  have hsub : J ⊆ Z.biUnion (fun v => (S.erase v).image (fun w => ({v, w} : Finset V))) := by
    intro e he
    obtain ⟨v, hvZ, hve⟩ := hhit e he
    obtain ⟨w, hvw, rfl⟩ := edge_other (hJ e he) hve
    have hwS : w ∈ S := hJS {v, w} he (by simp)
    exact mem_biUnion.mpr ⟨v, hvZ, mem_image.mpr ⟨w, by simp [hwS, hvw.symm], rfl⟩⟩
  calc
    J.card ≤ (Z.biUnion (fun v => (S.erase v).image (fun w => ({v, w} : Finset V)))).card :=
      card_le_card hsub
    _ ≤ ∑ v ∈ Z, ((S.erase v).image (fun w => ({v, w} : Finset V))).card := card_biUnion_le
    _ ≤ ∑ v ∈ Z, (S.card - 1) := by
      apply sum_le_sum
      intro v hv
      exact card_image_le.trans (by rw [card_erase_of_mem (hZ hv)])
    _ = (S.card - 1) * Z.card := by simp [mul_comm]

def oldSelected (F : Finset (Finset (V ⊕ C))) : Finset (Finset V) :=
  (F.filter (fun e => e.toRight = ∅)).image Finset.toLeft

def spokeVertices (S : Finset V) (F : Finset (Finset (V ⊕ C))) (c : C) : Finset V :=
  S.filter (fun v => spoke c v ∈ F)

theorem left_clique {H : SimpleGraph V} {S : Finset V} {n : ℕ} {e : Finset (V ⊕ C)}
    (he : (attached H S C).IsNClique n e) : H.IsClique e.toLeft := by
  intro a ha b hb hne
  exact he.isClique (mem_toLeft.mp ha) (mem_toLeft.mp hb) (fun h => hne (Sum.inl.inj h))

theorem right_empty_of_subset_lift {e : Finset (V ⊕ C)} {t : Finset V}
    (hsub : e ⊆ lift t) : e.toRight = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro c hc
  exact inr_not_mem_lift (hsub (mem_toRight.mp hc))

theorem oldSelected_cover {H : SimpleGraph V} {S : Finset V}
    {F : Finset (Finset (V ⊕ C))} (hF : IsCover (attached H S C) F) :
    IsCover H (oldSelected F) := by
  constructor
  · intro e he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    obtain ⟨hfF, hright⟩ := mem_filter.mp hf
    refine ⟨left_clique (hF.1 f hfF), ?_⟩
    have hh := card_toLeft_add_card_toRight (u := f)
    simpa [hright, (hF.1 f hfF).card_eq] using hh
  · intro t ht
    obtain ⟨e, he, hsub⟩ := hF.2 (lift t) (lift_triangle ht)
    refine ⟨e.toLeft, mem_image.mpr ⟨e,
      mem_filter.mpr ⟨he, right_empty_of_subset_lift hsub⟩, rfl⟩, ?_⟩
    intro v hv
    exact inl_mem_lift.mp (hsub (mem_toLeft.mp hv))

/-- Every selected-spoke set covers every residual neighborhood edge. -/
theorem spokes_hit_residual {H : SimpleGraph V} {S : Finset V}
    {F : Finset (Finset (V ⊕ C))} (hF : IsCover (attached H S C) F)
    {e : Finset V} (he : H.IsNClique 2 e) (heS : e ⊆ S)
    (hmissing : e ∉ oldSelected F) (c : C) :
    ∃ v ∈ spokeVertices S F c, v ∈ e := by
  obtain ⟨f, hf, hsub⟩ := hF.2 (cone (fun _ => c) e) (cone_triangle he heS (fun _ => c))
  have hfc := (hF.1 f hf).card_eq
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hfc
  have ha := hsub (by simp : a ∈ ({a, b} : Finset (V ⊕ C)))
  have hb := hsub (by simp : b ∈ ({a, b} : Finset (V ⊕ C)))
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hsub' : ({Sum.inl a, Sum.inl b} : Finset (V ⊕ C)) ⊆ lift e :=
        pair_subset_from_mem (inl_mem_lift.mpr (inl_mem_cone.mp ha))
          (inl_mem_lift.mpr (inl_mem_cone.mp hb))
      have heq : ({Sum.inl a, Sum.inl b} : Finset (V ⊕ C)) = lift e :=
        eq_of_subset_of_card_le hsub' (by rw [lift_card, he.card_eq, card_pair hab])
      have hm : e ∈ oldSelected F := by
        apply mem_image.mpr
        refine ⟨lift e, mem_filter.mpr ⟨?_, lift_right e⟩, lift_left e⟩
        rw [← heq]
        exact hf
      exact False.elim (hmissing hm)
    | inr b =>
      have hbc : b = c := inr_mem_cone.mp hb
      subst b
      exact ⟨a, mem_filter.mpr ⟨heS (inl_mem_cone.mp ha), hf⟩, inl_mem_cone.mp ha⟩
  | inr a =>
    cases b with
    | inl b =>
      have hac : a = c := inr_mem_cone.mp ha
      subst a
      refine ⟨b, mem_filter.mpr ⟨heS (inl_mem_cone.mp hb), ?_⟩, inl_mem_cone.mp hb⟩
      simpa [spoke, pair_comm] using hf
    | inr b =>
      exact False.elim (hab (congrArg Sum.inr
        ((inr_mem_cone.mp ha).trans (inr_mem_cone.mp hb).symm)))

/-- Old selected edges and the selected spokes are disjoint costs inside F. -/
theorem selected_cost_bound [Fintype C] (S : Finset V) (F : Finset (Finset (V ⊕ C))) :
    (oldSelected F).card + ∑ c : C, (spokeVertices S F c).card ≤ F.card := by
  classical
  let A := F.filter (fun e => e.toRight = ∅)
  let B := (univ : Finset C).biUnion (fun c => (spokeVertices S F c).image (spoke c))
  have hdisj : ((univ : Finset C) : Set C).PairwiseDisjoint (fun c => (spokeVertices S F c).image (spoke c)) := by
    intro c hc d hd hne
    apply disjoint_left.mpr
    intro e he hf
    obtain ⟨v, hv, rfl⟩ := mem_image.mp he
    obtain ⟨w, hw, hwe⟩ := mem_image.mp hf
    exact hne (spoke_center_eq hwe.symm)
  have hBcard : B.card = ∑ c : C, (spokeVertices S F c).card := by
    rw [show B = (univ : Finset C).biUnion (fun c => (spokeVertices S F c).image (spoke c)) from rfl,
      card_biUnion hdisj]
    apply sum_congr rfl
    intro c hc
    exact card_image_of_injective _ (spoke_injective c)
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro e he hf
    obtain ⟨c, hc, hec⟩ := mem_biUnion.mp hf
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hec
    have hh := (mem_filter.mp he).2
    simpa using hh
  have hsub : A ∪ B ⊆ F := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact (mem_filter.mp he).1
    · obtain ⟨c, hc, hec⟩ := mem_biUnion.mp he
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hec
      exact (mem_filter.mp hv).2
  calc
    (oldSelected F).card + ∑ c : C, (spokeVertices S F c).card ≤ A.card + B.card :=
      Nat.add_le_add card_image_le (by rw [hBcard])
    _ = (A ∪ B).card := (card_union_of_disjoint hAB).symm
    _ ≤ F.card := card_le_card hsub

/-- Replace all selected spokes by residual neighborhood edges at no additional cost. -/
theorem replace_spokes [Fintype C] [Nonempty C] (H : SimpleGraph V) (S : Finset V)
    (hC : S.card - 1 ≤ Fintype.card C)
    (F : Finset (Finset (V ⊕ C))) (hF : IsCover (attached H S C) F) :
    ∃ B : Finset (Finset V), IsCover H B ∧
      (∀ e : Finset V, H.IsNClique 2 e → e ⊆ S → e ∈ B) ∧ B.card ≤ F.card := by
  classical
  let J := (S.powersetCard 2).filter (fun e => H.IsNClique 2 e ∧ e ∉ oldSelected F)
  have hJ : ∀ e ∈ J, H.IsNClique 2 e := fun e he => (mem_filter.mp he).2.1
  have hJS : ∀ e ∈ J, e ⊆ S := fun e he => (mem_powersetCard.mp (mem_filter.mp he).1).1
  have hhit : ∀ c : C, ∀ e ∈ J, ∃ v ∈ spokeVertices S F c, v ∈ e := by
    intro c e he
    exact spokes_hit_residual hF (hJ e he) (hJS e he) (mem_filter.mp he).2.2 c
  obtain ⟨c, hc, hmin⟩ := exists_min_image (univ : Finset C)
    (fun c => (spokeVertices S F c).card) univ_nonempty
  have hJcost : J.card ≤ ∑ d : C, (spokeVertices S F d).card := by
    calc
      J.card ≤ (S.card - 1) * (spokeVertices S F c).card :=
        edge_cover_cost S _ J (filter_subset _ _) (fun e he => (hJ e he).card_eq) hJS (hhit c)
      _ ≤ Fintype.card C * (spokeVertices S F c).card := Nat.mul_le_mul_right _ hC
      _ = ∑ d : C, (spokeVertices S F c).card := by simp
      _ ≤ ∑ d : C, (spokeVertices S F d).card := sum_le_sum (fun d hd => hmin d hd)
  have hOld := oldSelected_cover hF
  refine ⟨oldSelected F ∪ J, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro e he
    rcases mem_union.mp he with he | he
    · exact hOld.1 e he
    · exact hJ e he
  · intro t ht
    obtain ⟨e, he, hesub⟩ := hOld.2 t ht
    exact ⟨e, mem_union_left _ he, hesub⟩
  · intro e he heS
    by_cases hmem : e ∈ oldSelected F
    · exact mem_union_left _ hmem
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_powersetCard.mpr ⟨heS, he.card_eq⟩, he, hmem⟩)
  · calc
      (oldSelected F ∪ J).card ≤ (oldSelected F).card + J.card := card_union_le _ _
      _ ≤ (oldSelected F).card + ∑ d : C, (spokeVertices S F d).card := Nat.add_le_add_left hJcost _
      _ ≤ F.card := selected_cost_bound S F

/-- A saturated old-edge cover works for any number of new centers. -/
theorem lift_saturated_cover {H : SimpleGraph V} {S : Finset V}
    {B : Finset (Finset V)} (hB : IsCover H B)
    (hsat : ∀ e : Finset V, H.IsNClique 2 e → e ⊆ S → e ∈ B) :
    IsCover (attached H S D) (B.image (lift (C := D))) := by
  constructor
  · intro e he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    constructor
    · intro a ha b hb hne
      obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
      exact (hB.1 f hf).isClique hx hy (fun h => hne (congrArg Sum.inl h))
    · simpa using (hB.1 f hf).card_eq
  · intro t ht
    by_cases hr : t.toRight = ∅
    · have hleft : H.IsNClique 3 t.toLeft := ⟨left_isClique ht, left_card_old ht hr⟩
      obtain ⟨e, he, hesub⟩ := hB.2 _ hleft
      exact ⟨lift e, mem_image.mpr ⟨e, he, rfl⟩, lift_subset_of_left hesub⟩
    · have he : H.IsNClique 2 t.toLeft := ⟨left_isClique ht, left_card_new ht hr⟩
      exact ⟨lift t.toLeft,
        mem_image.mpr ⟨t.toLeft, hsat _ he (left_subset_neighborhood ht hr), rfl⟩,
        lift_subset_of_left (Subset.refl _)⟩

/-- A cover at |S|-1 centers extends, without extra edges, to any target multiplicity. -/
theorem extend_cover (H : SimpleGraph V) (S : Finset V) (hs : 2 ≤ S.card)
    (F : Finset (Finset (V ⊕ Fin (S.card - 1))))
    (hF : IsCover (attached H S (Fin (S.card - 1))) F) :
    ∃ R : Finset (Finset (V ⊕ D)), IsCover (attached H S D) R ∧ R.card ≤ F.card := by
  classical
  letI : NeZero (S.card - 1) := ⟨by omega⟩
  obtain ⟨B, hB, hsat, hcost⟩ := replace_spokes H S (by simp) F hF
  exact ⟨B.image (lift (C := D)), lift_saturated_cover hB hsat, card_image_le.trans hcost⟩

#print axioms edge_cover_cost
#print axioms replace_spokes
#print axioms extend_cover

/-- Pull two vertices back from the image of a finite set. -/
theorem preimage_edge (f : V → W) {e : Finset W} {t : Finset V}
    (he : e.card = 2) (hsub : e ⊆ t.image f) :
    ∃ d : Finset V, d ⊆ t ∧ d.card = 2 ∧ d.image f = e := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp he
  obtain ⟨x, hx, hfx⟩ := mem_image.mp (hsub (by simp : a ∈ ({a, b} : Finset W)))
  obtain ⟨y, hy, hfy⟩ := mem_image.mp (hsub (by simp : b ∈ ({a, b} : Finset W)))
  have hxy : x ≠ y := by
    intro h
    exact hab (hfx.symm.trans ((congrArg f h).trans hfy))
  exact ⟨{x, y}, pair_subset_from_mem hx hy, card_pair hxy, by simp [hfx, hfy]⟩

theorem image_clique {H : SimpleGraph V} {K : SimpleGraph W} (f : V → W)
    (hf : Function.Injective f) (hadj : ∀ a b, H.Adj a b → K.Adj (f a) (f b))
    {n : ℕ} {t : Finset V} (ht : H.IsNClique n t) : K.IsNClique n (t.image f) := by
  constructor
  · intro a ha b hb hne
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
    exact hadj x y (ht.isClique hx hy (fun h => hne (congrArg f h)))
  · rw [card_image_of_injective t hf, ht.card_eq]

/-- Restriction along an injective graph map cannot increase a cover's size. -/
theorem pullback_cover [Fintype V] {H : SimpleGraph V} {K : SimpleGraph W}
    (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ a b, H.Adj a b → K.Adj (f a) (f b))
    {F : Finset (Finset W)} (hF : IsCover K F) :
    ∃ E : Finset (Finset V), IsCover H E ∧ E.card ≤ F.card := by
  classical
  let E := (univ : Finset V).powersetCard 2 |>.filter
    (fun e => H.IsNClique 2 e ∧ e.image f ∈ F)
  refine ⟨E, ⟨?_, ?_⟩, ?_⟩
  · intro e he
    exact (mem_filter.mp he).2.1
  · intro t ht
    obtain ⟨e, he, hesub⟩ := hF.2 (t.image f) (image_clique f hf hadj ht)
    obtain ⟨d, hdsub, hdcard, hdimage⟩ := preimage_edge f (hF.1 e he).card_eq hesub
    have hd : H.IsNClique 2 d := ⟨by
      intro a ha b hb hne
      exact ht.isClique (hdsub ha) (hdsub hb) hne, hdcard⟩
    refine ⟨d, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hdcard⟩, hd, ?_⟩, hdsub⟩
    simpa only [hdimage] using he
  · calc
      E.card = (E.image (fun e => e.image f)).card :=
        (card_image_of_injective E (TuzaGraphCompression.image_injective hf)).symm
      _ ≤ F.card := card_le_card (by
        intro e he
        obtain ⟨d, hd, rfl⟩ := mem_image.mp he
        exact (mem_filter.mp hd).2.2)

theorem restrict_centers [Fintype V] (H : SimpleGraph V) (S : Finset V) {m n : ℕ}
    (hmn : m ≤ n) {F : Finset (Finset (V ⊕ Fin n))} (hF : IsCover (attached H S (Fin n)) F) :
    ∃ E : Finset (Finset (V ⊕ Fin m)), IsCover (attached H S (Fin m)) E ∧ E.card ≤ F.card := by
  let f : Fin m → Fin n := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun x : Fin n => x.val) h
  exact pullback_cover (centerMap f) (centerMap_injective hf) (centerMap_adj H S f) hF

def CoverBudget (H : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ F : Finset (Finset V), IsCover H F ∧ F.card ≤ n

/-- Covers within a given budget exist before compression exactly when they exist after it. -/
theorem coverBudget_attached_min [Fintype V] (H : SimpleGraph V) (S : Finset V)
    (hs : 2 ≤ S.card) (m n : ℕ) : CoverBudget (attached H S (Fin m)) n ↔
      CoverBudget (attached H S (Fin (min m (S.card - 1)))) n := by
  by_cases hm : m ≤ S.card - 1
  · rw [Nat.min_eq_left hm]
  · have hh : S.card - 1 ≤ m := by omega
    rw [Nat.min_eq_right hh]
    constructor
    · rintro ⟨F, hF, hcost⟩
      obtain ⟨E, hE, hEc⟩ := restrict_centers H S hh hF
      exact ⟨E, hE, hEc.trans hcost⟩
    · rintro ⟨F, hF, hcost⟩
      obtain ⟨E, hE, hEc⟩ := extend_cover (D := Fin m) H S hs F hF
      exact ⟨E, hE, hEc.trans hcost⟩

theorem exists_cover [Fintype V] (H : SimpleGraph V) : ∃ F : Finset (Finset V), IsCover H F := by
  classical
  refine ⟨H.cliqueFinset 2, ⟨?_, ?_⟩⟩
  · intro e he
    exact SimpleGraph.mem_cliqueFinset_iff.mp he
  · intro t ht
    obtain ⟨e, hesub, hecard⟩ := exists_subset_card_eq (show 2 ≤ t.card by rw [ht.card_eq]; decide)
    refine ⟨e, SimpleGraph.mem_cliqueFinset_iff.mpr ⟨?_, hecard⟩, hesub⟩
    intro a ha b hb hne
    exact ht.isClique (hesub ha) (hesub hb) hne

theorem exists_cover_budget [Fintype V] (H : SimpleGraph V) : ∃ n : ℕ, CoverBudget H n := by
  obtain ⟨F, hF⟩ := exists_cover H
  exact ⟨F.card, F, hF, le_rfl⟩

/-- The least possible number of actual graph edges meeting all triangles. -/
noncomputable def coverNumber [Fintype V] (H : SimpleGraph V) : ℕ := by
  classical
  exact Nat.find (exists_cover_budget H)

theorem coverNumber_budget [Fintype V] (H : SimpleGraph V) : CoverBudget H (coverNumber H) := by
  classical
  exact Nat.find_spec (exists_cover_budget H)

theorem coverNumber_le_of_budget [Fintype V] {H : SimpleGraph V} {n : ℕ}
    (h : CoverBudget H n) : coverNumber H ≤ n := by
  classical
  exact Nat.find_min' (exists_cover_budget H) h

/-- The minimum is attained, and every valid graph cover costs at least this much. -/
theorem coverNumber_spec [Fintype V] (H : SimpleGraph V) :
    ∃ F : Finset (Finset V), IsCover H F ∧ F.card = coverNumber H ∧
      ∀ E : Finset (Finset V), IsCover H E → coverNumber H ≤ E.card := by
  obtain ⟨F, hF, hcost⟩ := coverNumber_budget H
  refine ⟨F, hF, le_antisymm hcost (coverNumber_le_of_budget ⟨F, hF, le_rfl⟩), ?_⟩
  intro E hE
  exact coverNumber_le_of_budget ⟨E, hE, le_rfl⟩

/-- Exact cover multiplicity compression for every finite graph and every m. -/
theorem coverNumber_attached_min [Fintype V] (H : SimpleGraph V) (S : Finset V)
    (hs : 2 ≤ S.card) (m : ℕ) : coverNumber (attached H S (Fin m)) =
      coverNumber (attached H S (Fin (min m (S.card - 1)))) := by
  apply le_antisymm
  · exact coverNumber_le_of_budget ((coverBudget_attached_min H S hs m _).mpr
      (coverNumber_budget (attached H S (Fin (min m (S.card - 1))))))
  · exact coverNumber_le_of_budget ((coverBudget_attached_min H S hs m _).mp
      (coverNumber_budget (attached H S (Fin m))))

/-- One common cap preserves both graph optimization parameters simultaneously. -/
theorem both_parameters_attached_min [Fintype V] (H : SimpleGraph V) (S : Finset V)
    (hs : 2 ≤ S.card) (m : ℕ) :
    packingNumber (attached H S (Fin m)) =
      packingNumber (attached H S (Fin (min m (colorCount S.card)))) ∧
    coverNumber (attached H S (Fin m)) =
      coverNumber (attached H S (Fin (min m (colorCount S.card)))) := by
  refine ⟨packingNumber_attached_min H S hs m, ?_⟩
  have hr : S.card - 1 ≤ colorCount S.card := by unfold colorCount; split <;> omega
  have hmin : min (min m (colorCount S.card)) (S.card - 1) = min m (S.card - 1) := by
    rw [Nat.min_assoc, Nat.min_eq_right hr]
  have hh := coverNumber_attached_min H S hs (min m (colorCount S.card))
  rw [hmin] at hh
  exact (coverNumber_attached_min H S hs m).trans hh.symm

#print axioms pullback_cover
#print axioms coverBudget_attached_min
#print axioms coverNumber_spec
#print axioms coverNumber_attached_min
#print axioms both_parameters_attached_min
#check both_parameters_attached_min
end TuzaCoverCompression

/-!
Explicit cut covers with exact costs, including arbitrary outer neighborhoods.
OpenAI Codex (GPT-6 Astra), 2026-10-07.
-/
namespace TuzaCutCovers
open Finset TuzaCompression TuzaGraphCompression TuzaCoverCompression
  TuzaIndependentAllocation

variable {V W C D : Type*} [DecidableEq V] [DecidableEq W]
  [DecidableEq C] [DecidableEq D]

def splitGraph (N : C → Finset V) : SimpleGraph (V ⊕ C) where
  Adj a b := match a, b with
    | .inl v, .inl w => v ≠ w
    | .inl v, .inr c => v ∈ N c
    | .inr c, .inl v => v ∈ N c
    | .inr _, .inr _ => False
  symm.symm a b h := by
    cases a <;> cases b
    · exact h.symm
    · exact h
    · exact h
    · exact h
  loopless.irrefl a := by cases a <;> simp

def side (A S : Finset V) (b : Bool) : Finset V :=
  if b then S ∩ A else S \ A

@[simp] theorem mem_side (A S : Finset V) (b : Bool) (v : V) :
    v ∈ side A S b ↔ v ∈ S ∧ decide (v ∈ A) = b := by
  cases b <;> simp [side]

def coreEdges [Fintype V] (A : Finset V) : Finset (Finset V) :=
  A.powersetCard 2 ∪ (univ \ A).powersetCard 2

theorem coreEdges_card [Fintype V] (A : Finset V) :
    (coreEdges A).card = A.card.choose 2 + (Fintype.card V - A.card).choose 2 := by
  have hd : Disjoint (A.powersetCard 2) ((univ \ A).powersetCard 2) := by
    apply disjoint_left.mpr
    intro e he hf
    obtain ⟨hes, hec⟩ := mem_powersetCard.mp he
    obtain ⟨hfs, _⟩ := mem_powersetCard.mp hf
    obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < e.card)
    exact (mem_sdiff.mp (hfs hv)).2 (hes hv)
  rw [coreEdges, card_union_of_disjoint hd, card_powersetCard, card_powersetCard,
    card_sdiff_of_subset (subset_univ A), card_univ]

def spokeEdges [Fintype C] (A : Finset V) (N : C → Finset V) (b : C → Bool) :
    Finset (Finset (V ⊕ C)) :=
  univ.biUnion (fun c => (side A (N c) (b c)).image (spoke c))

theorem spokeEdges_card [Fintype C] (A : Finset V) (N : C → Finset V) (b : C → Bool) :
    (spokeEdges A N b).card = ∑ c, (side A (N c) (b c)).card := by
  unfold spokeEdges
  rw [card_biUnion]
  · apply sum_congr rfl
    intro c hc
    exact card_image_of_injective _ (spoke_injective c)
  · intro c hc d hd hcd
    apply disjoint_left.mpr
    intro e he hf
    obtain ⟨v, hv, hve⟩ := mem_image.mp he
    obtain ⟨w, hw, hwe⟩ := mem_image.mp hf
    exact hcd (spoke_center_eq (hve.trans hwe.symm))

def cutEdges [Fintype V] [Fintype C] (A : Finset V) (N : C → Finset V)
    (b : C → Bool) : Finset (Finset (V ⊕ C)) :=
  (coreEdges A).image (lift (C := C)) ∪ spokeEdges A N b

theorem cutEdges_card [Fintype V] [Fintype C] (A : Finset V) (N : C → Finset V)
    (b : C → Bool) : (cutEdges A N b).card =
      A.card.choose 2 + (Fintype.card V - A.card).choose 2 +
        ∑ c, (side A (N c) (b c)).card := by
  have hd : Disjoint ((coreEdges A).image (lift (C := C))) (spokeEdges A N b) := by
    apply disjoint_left.mpr
    intro e he hf
    obtain ⟨d, hd, rfl⟩ := mem_image.mp he
    obtain ⟨c, hc, hce⟩ := mem_biUnion.mp hf
    obtain ⟨v, hv, hve⟩ := mem_image.mp hce
    have hh := congrArg Finset.toRight hve
    simpa using hh
  rw [cutEdges, card_union_of_disjoint hd,
    card_image_of_injective _ lift_injective, coreEdges_card, spokeEdges_card]

/-- Two colors force a same-color pair in every three-element set. -/
theorem monochromatic_pair (t : Finset W) (ht : t.card = 3) (color : W → Bool) :
    ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ color a = color b := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp ht
  by_cases hAB : color a = color b
  · exact ⟨a, by simp, b, by simp, hab, hAB⟩
  by_cases hAC : color a = color c
  · exact ⟨a, by simp, c, by simp, hac, hAC⟩
  have hBC : color b = color c := by
    cases ha : color a <;> cases hb : color b <;> cases hc : color c <;>
      simp_all
  exact ⟨b, by simp, c, by simp, hbc, hBC⟩

theorem cover_of_same_color (G : SimpleGraph W) (color : W → Bool)
    (F : Finset (Finset W)) (hedge : ∀ e ∈ F, G.IsNClique 2 e)
    (hmono : ∀ a b, G.Adj a b → color a = color b → {a,b} ∈ F) : IsCover G F := by
  refine ⟨hedge, ?_⟩
  intro t ht
  obtain ⟨a, ha, b, hb, hab, hc⟩ := monochromatic_pair t ht.card_eq color
  exact ⟨{a,b}, hmono a b (ht.isClique ha hb hab) hc, pair_subset_from_mem ha hb⟩

theorem pair_mem_coreEdges [Fintype V] (A : Finset V) {a b : V} (hab : a ≠ b)
    (hcolor : decide (a ∈ A) = decide (b ∈ A)) : {a,b} ∈ coreEdges A := by
  by_cases ha : a ∈ A
  · have hb : b ∈ A := by simpa [ha] using hcolor.symm
    exact mem_union_left _ (mem_powersetCard.mpr ⟨pair_subset_from_mem ha hb, card_pair hab⟩)
  · have hb : b ∉ A := by simpa [ha] using hcolor.symm
    exact mem_union_right _ (mem_powersetCard.mpr
      ⟨pair_subset_from_mem (by simp [ha]) (by simp [hb]), card_pair hab⟩)

theorem spoke_mem_cutEdges [Fintype V] [Fintype C] (A : Finset V)
    (N : C → Finset V) (b : C → Bool) {v : V} {c : C}
    (hv : v ∈ N c) (hc : decide (v ∈ A) = b c) : spoke c v ∈ cutEdges A N b := by
  exact mem_union_right _ (mem_biUnion.mpr ⟨c, mem_univ c,
    mem_image.mpr ⟨v, (mem_side A (N c) (b c) v).mpr ⟨hv,hc⟩, rfl⟩⟩)

/-- The deleted edges are actual graph edges and meet every triangle. -/
theorem cutEdges_isCover [Fintype V] [Fintype C] (A : Finset V)
    (N : C → Finset V) (b : C → Bool) : IsCover (splitGraph N) (cutEdges A N b) := by
  let color : V ⊕ C → Bool := Sum.elim (fun v => decide (v ∈ A)) b
  apply cover_of_same_color (splitGraph N) color (cutEdges A N b)
  · intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨d, hd, rfl⟩ := mem_image.mp he
      have hdc : d.card = 2 := by
        rcases mem_union.mp hd with hd | hd
        · exact (mem_powersetCard.mp hd).2
        · exact (mem_powersetCard.mp hd).2
      apply image_clique Sum.inl Sum.inl_injective
        (H := (⊤ : SimpleGraph V)) (K := splitGraph N)
      · intro a b hab
        exact hab
      · exact ⟨by intro a ha b hb hab; exact hab, hdc⟩
    · obtain ⟨c, hc, hce⟩ := mem_biUnion.mp he
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hce
      change (splitGraph N).IsNClique 2 {Sum.inl v, Sum.inr c}
      refine ⟨?_, card_pair (by simp)⟩
      rw [coe_pair]
      exact SimpleGraph.isClique_pair.mpr (fun _ => ((mem_side _ _ _ _).mp hv).1)
  · intro a d hadj hc
    cases a with
    | inl v =>
      cases d with
      | inl w =>
        have he := pair_mem_coreEdges A hadj hc
        apply mem_union_left
        exact mem_image.mpr ⟨{v,w}, he, by simp [lift]⟩
      | inr c => exact spoke_mem_cutEdges A N b hadj hc
    | inr c =>
      cases d with
      | inl v =>
        simpa only [spoke, pair_comm] using spoke_mem_cutEdges A N b hadj hc.symm
      | inr d => exact False.elim hadj

/-- Every prescribed core cut and outer side assignment has this exact cost. -/
theorem explicit_cut [Fintype V] [Fintype C] (A : Finset V)
    (N : C → Finset V) (b : C → Bool) :
    ∃ F, IsCover (splitGraph N) F ∧ F.card =
      A.card.choose 2 + (Fintype.card V - A.card).choose 2 +
        ∑ c, (side A (N c) (b c)).card :=
  ⟨cutEdges A N b, cutEdges_isCover A N b, cutEdges_card A N b⟩

def cheaperSide (A S : Finset V) : Bool := decide ((S ∩ A).card ≤ (S \ A).card)

theorem cheaperSide_card (A S : Finset V) :
    (side A S (cheaperSide A S)).card = min (S ∩ A).card (S \ A).card := by
  by_cases h : (S ∩ A).card ≤ (S \ A).card
  · simp [cheaperSide, side, h]
  · simp [cheaperSide, side, h, Nat.min_eq_right (by omega : (S \ A).card ≤ (S ∩ A).card)]

theorem splitGraph_twoAttached (S T : Finset V) :
    splitGraph (neighborhood S T : C ⊕ D → Finset V) =
      twoAttached (⊤ : SimpleGraph V) S T C D := by
  ext a b
  cases a <;> cases b <;> simp [splitGraph, twoAttached]

/-- Optimize each outer type separately while retaining an actual cover witness. -/
theorem two_type_cut [Fintype V] (A S T : Finset V) (m n : ℕ) :
    ∃ F, IsCover (twoAttached (⊤ : SimpleGraph V) S T (Fin m) (Fin n)) F ∧
      F.card = A.card.choose 2 + (Fintype.card V - A.card).choose 2 +
        m * min (S ∩ A).card (S \ A).card + n * min (T ∩ A).card (T \ A).card := by
  let N : Fin m ⊕ Fin n → Finset V := neighborhood S T
  let b : Fin m ⊕ Fin n → Bool := Sum.elim (fun _ => cheaperSide A S) (fun _ => cheaperSide A T)
  obtain ⟨F, hF, hc⟩ := explicit_cut A N b
  refine ⟨F, ?_, ?_⟩
  · simpa only [N, splitGraph_twoAttached] using hF
  · simpa [N, b, neighborhood, Fintype.sum_sum_type, cheaperSide_card, Nat.add_assoc] using hc

theorem two_type_cover_bound [Fintype V] (A S T : Finset V) (m n : ℕ) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin m) (Fin n)) ≤
      A.card.choose 2 + (Fintype.card V - A.card).choose 2 +
        m * min (S ∩ A).card (S \ A).card + n * min (T ∩ A).card (T \ A).card := by
  obtain ⟨F,hF,hc⟩ := two_type_cut A S T m n
  exact coverNumber_le_of_budget ⟨F,hF,hc.le⟩

/-- An integer cut contained in both neighborhoods yields the common-cut cost. -/
theorem common_cut [Fintype V] (A S T : Finset V) (hAS : A ⊆ S) (hAT : A ⊆ T)
    (m n : ℕ) : ∃ F,
    IsCover (twoAttached (⊤ : SimpleGraph V) S T (Fin m) (Fin n)) F ∧
      F.card = A.card.choose 2 + (Fintype.card V - A.card).choose 2 +
        m * (S.card - A.card) + n * (T.card - A.card) := by
  let N : Fin m ⊕ Fin n → Finset V := neighborhood S T
  obtain ⟨F,hF,hc⟩ := explicit_cut A N (fun _ => false)
  refine ⟨F,?_,?_⟩
  · simpa only [N, splitGraph_twoAttached] using hF
  · simpa [N, neighborhood, Fintype.sum_sum_type, side,
      card_sdiff_of_subset hAS, card_sdiff_of_subset hAT, Nat.add_assoc] using hc

theorem common_cut_size [Fintype V] (S T : Finset V) (m n j : ℕ)
    (hj : j ≤ (S ∩ T).card) : ∃ F,
    IsCover (twoAttached (⊤ : SimpleGraph V) S T (Fin m) (Fin n)) F ∧
      F.card = j.choose 2 + (Fintype.card V - j).choose 2 +
        m * (S.card - j) + n * (T.card - j) := by
  obtain ⟨A,hA,hAc⟩ := exists_subset_card_eq hj
  obtain ⟨F,hF,hc⟩ := common_cut A S T (fun v hv => (mem_inter.mp (hA hv)).1)
    (fun v hv => (mem_inter.mp (hA hv)).2) m n
  exact ⟨F,hF,by simpa only [hAc] using hc⟩

#print axioms coreEdges_card
#print axioms spokeEdges_card
#print axioms cutEdges_card
#print axioms cover_of_same_color
#print axioms cutEdges_isCover
#print axioms explicit_cut
#print axioms two_type_cut
#print axioms two_type_cover_bound
#print axioms common_cut_size
#check two_type_cover_bound
end TuzaCutCovers

/-!
Deterministic common-neighborhood rounding with an actual cover witness.
OpenAI Codex (GPT-6 Astra), 2026-10-07.
-/
namespace TuzaCommonRounding
open Finset TuzaCoverCompression TuzaCutCovers TuzaIndependentAllocation

variable {V : Type*} [DecidableEq V]

/-- The real polynomial formula includes the cases n=0 and n=1. -/
theorem choose_two_real (n : ℕ) : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ)-1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hc : (n+1).choose 2 = n + n.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' n 1
    simp only [Nat.succ_eq_add_one, hc, Nat.cast_add, Nat.cast_one, ih]
    ring

def commonCost (k s t p q j : ℕ) : ℕ :=
  j.choose 2 + (k-j).choose 2 + p*(s-j) + q*(t-j)

/-- The natural-number count and the real quadratic agree on every feasible cut. -/
theorem commonCost_real (k s t p q j : ℕ) (hk : j ≤ k) (hs : j ≤ s) (ht : j ≤ t) :
    (commonCost k s t p q j : ℝ) =
      (k.choose 2 : ℝ) + (p : ℝ)*s + (q : ℝ)*t -
        (j : ℝ)*((k : ℝ)+p+q) + (j : ℝ)^2 := by
  simp only [commonCost, Nat.cast_add, Nat.cast_mul, choose_two_real,
    Nat.cast_sub hk, Nat.cast_sub hs, Nat.cast_sub ht]
  ring

def roundedSize (B u : ℕ) : ℕ := min u (B/2)

theorem roundedSize_le (B u : ℕ) : roundedSize B u ≤ u := Nat.min_le_left _ _

/-- The floor of an integer divided by two misses its real half by at most 1/2. -/
theorem half_bounds (B : ℕ) :
    0 ≤ (B : ℝ) - 2*(B/2 : ℕ) ∧ (B : ℝ) - 2*(B/2 : ℕ) ≤ 1 := by
  have h0 : 2*(B/2) ≤ B := by omega
  have h1 : B ≤ 2*(B/2)+1 := by omega
  have h0r : 2*((B/2 : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast h0
  have h1r : (B : ℝ) ≤ 2*(B/2 : ℕ)+1 := by exact_mod_cast h1
  constructor <;> linarith

/-- One fixed feasible integer cut works simultaneously for every real x <= u. -/
theorem rounded_quadratic (B u : ℕ) (x : ℝ) (hx : x ≤ (u : ℝ)) :
    (roundedSize B u : ℝ)^2 - (B : ℝ)*(roundedSize B u) ≤
      x^2 - (B : ℝ)*x + 1/4 := by
  obtain ⟨h0,h1⟩ := half_bounds B
  by_cases hu : u ≤ B/2
  · rw [roundedSize, Nat.min_eq_left hu]
    have hub : (u : ℝ) ≤ (B/2 : ℕ) := by exact_mod_cast hu
    have hp : 0 ≤ ((u : ℝ)-x)*((B : ℝ)-u-x) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · rw [roundedSize, Nat.min_eq_right (by omega : B/2 ≤ u)]
    have hp : 0 ≤ ((B : ℝ)-2*(B/2 : ℕ))*(1-((B : ℝ)-2*(B/2 : ℕ))) :=
      mul_nonneg h0 (by linarith)
    nlinarith [sq_nonneg (2*x-(B : ℝ))]

/-- The chosen integer minimizes the quadratic over all feasible integer sizes. -/
theorem rounded_integer_min (B u r : ℕ) (hr : r ≤ u) :
    (roundedSize B u : ℝ)^2 - (B : ℝ)*(roundedSize B u) ≤
      (r : ℝ)^2 - (B : ℝ)*r := by
  let j := roundedSize B u
  have hjB : j ≤ B/2 := Nat.min_le_right _ _
  obtain ⟨h0,h1⟩ := half_bounds B
  have hjBr : (j : ℝ) ≤ (B/2 : ℕ) := by exact_mod_cast hjB
  change (j : ℝ)^2 - (B : ℝ)*j ≤ (r : ℝ)^2 - (B : ℝ)*r
  by_cases hrj : r ≤ j
  · have hrjr : (r : ℝ) ≤ j := by exact_mod_cast hrj
    have hp : 0 ≤ ((j : ℝ)-r)*((B : ℝ)-j-r) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have hju : B/2 ≤ u := by
      by_contra h
      have heq : j = u := Nat.min_eq_left (by omega)
      omega
    have hj : j = B/2 := Nat.min_eq_right hju
    have hrj1 : j+1 ≤ r := by omega
    have hrj1r : (j : ℝ)+1 ≤ r := by exact_mod_cast hrj1
    have hBj : (B : ℝ) ≤ 2*(j : ℝ)+1 := by rw [hj]; linarith
    have hp : 0 ≤ ((r : ℝ)-j)*((r : ℝ)+j-B) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- Actual cover at the rounded size, with a uniform real-parameter guarantee. -/
theorem common_cut_witness [Fintype V] (S T : Finset V) (p q : ℕ) :
    let k := Fintype.card V
    let j := roundedSize (k+p+q) (S ∩ T).card
    ∃ F, IsCover (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) F ∧
      F.card = commonCost k S.card T.card p q j ∧
      ∀ x : ℝ, x ≤ ((S ∩ T).card : ℝ) →
        (F.card : ℝ) ≤ (k.choose 2 : ℝ) + (p : ℝ)*S.card + (q : ℝ)*T.card -
          x*((k : ℝ)+p+q) + x^2 + 1/4 := by
  dsimp only
  let k := Fintype.card V
  let j := roundedSize (k+p+q) (S ∩ T).card
  have hju : j ≤ (S ∩ T).card := roundedSize_le _ _
  have hjS : j ≤ S.card := hju.trans (card_le_card inter_subset_left)
  have hjT : j ≤ T.card := hju.trans (card_le_card inter_subset_right)
  have hjk : j ≤ k := hjS.trans (card_le_univ S)
  obtain ⟨F,hF,hc⟩ := common_cut_size S T p q j hju
  have hcost : F.card = commonCost k S.card T.card p q j := hc
  refine ⟨F,hF,hcost,?_⟩
  intro x hx
  have hround := rounded_quadratic (k+p+q) (S ∩ T).card x hx
  have hpoly := commonCost_real k S.card T.card p q j hjk hjS hjT
  have hreal : (F.card : ℝ) = (commonCost k S.card T.card p q j : ℝ) := by rw [hcost]
  change (j : ℝ)^2 - ((k+p+q : ℕ) : ℝ)*(j : ℝ) ≤ x^2 - ((k+p+q : ℕ) : ℝ)*x + 1/4 at hround
  push_cast at hround
  nlinarith only [hreal,hpoly,hround]

/-- The written common-neighborhood cover bound, on the attained graph optimum. -/
theorem common_cover_bound [Fintype V] (S T : Finset V) (p q : ℕ)
    (x : ℝ) (hx : x ≤ ((S ∩ T).card : ℝ)) :
    (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) ≤
      ((Fintype.card V).choose 2 : ℝ) + (p : ℝ)*S.card + (q : ℝ)*T.card -
        x*((Fintype.card V : ℝ)+p+q) + x^2 + 1/4 := by
  obtain ⟨F,hF,hc,hbound⟩ := common_cut_witness S T p q
  have hmin : coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤ F.card :=
    coverNumber_le_of_budget ⟨F,hF,le_rfl⟩
  exact (show (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) ≤
    (F.card : ℝ) by exact_mod_cast hmin).trans (hbound x hx)

theorem clipped_square (B u : ℝ) :
    (min u (B/2))^2 - B*min u (B/2) = -B^2/4 + (max 0 (B/2-u))^2 := by
  by_cases h : u ≤ B/2
  · rw [min_eq_left h, max_eq_right (by linarith : 0 ≤ B/2-u)]
    ring
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h)), max_eq_left (by linarith : B/2-u ≤ 0)]
    ring

/-- Optimized form used by the subsequent common-neighborhood criterion. -/
theorem common_cover_optimized [Fintype V] (S T : Finset V) (p q : ℕ) :
    (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) ≤
      ((Fintype.card V).choose 2 : ℝ) + (p : ℝ)*S.card + (q : ℝ)*T.card -
        ((Fintype.card V : ℝ)+p+q)^2/4 +
        (max 0 (((Fintype.card V : ℝ)+p+q)/2 - (S ∩ T).card))^2 + 1/4 := by
  have h := common_cover_bound S T p q
    (min ((S ∩ T).card : ℝ) (((Fintype.card V : ℝ)+p+q)/2)) (min_le_left _ _)
  have hi := clipped_square ((Fintype.card V : ℝ)+p+q) (S ∩ T).card
  nlinarith only [h,hi]

#print axioms choose_two_real
#print axioms commonCost_real
#print axioms rounded_quadratic
#print axioms rounded_integer_min
#print axioms common_cut_witness
#print axioms common_cover_bound
#print axioms clipped_square
#print axioms common_cover_optimized
#check common_cover_optimized
end TuzaCommonRounding

/-!
Balanced rounding of an affine cut cost with an actual graph cover.
OpenAI Codex (GPT-6 Astra), 2026-10-07.
-/
namespace TuzaBalancedRounding
open Finset TuzaCoverCompression TuzaCutCovers TuzaCommonRounding
  TuzaIndependentAllocation

variable {V : Type*} [DecidableEq V]

/-- Ordered subset selection also works for arbitrary real, possibly negative weights. -/
theorem real_ordered_subset (w : V → ℝ) (r : ℕ) (s : Finset V) (hr : r ≤ s.card) :
    ∃ A ⊆ s, A.card = r ∧ ∀ a ∈ A, ∀ b ∈ s, b ∉ A → w a ≤ w b := by
  classical
  induction r generalizing s with
  | zero => exact ⟨∅, empty_subset _, by simp, by simp⟩
  | succ r ih =>
    have hs : s.Nonempty := card_pos.mp (by omega)
    obtain ⟨x, hx, hmin⟩ := exists_min_image s w hs
    obtain ⟨A, hAs, hAc, horder⟩ := ih (s.erase x) (by rw [card_erase_of_mem hx]; omega)
    have hxA : x ∉ A := fun h => (mem_erase.mp (hAs h)).1 rfl
    refine ⟨insert x A, ?_, ?_, ?_⟩
    · intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · exact hx
      · exact (mem_erase.mp (hAs ha)).2
    · rw [card_insert_of_notMem hxA, hAc]
    · intro a ha b hb hbA
      rcases mem_insert.mp ha with rfl | ha
      · exact hmin b hb
      · have hbx : b ≠ x := by
          intro hh
          apply hbA
          simp [hh]
        exact horder a ha b (mem_erase.mpr ⟨hbx,hb⟩)
          (fun hh => hbA (mem_insert_of_mem hh))

theorem sum_if_mem_subset (A s : Finset V) (f : V → ℝ) (hAs : A ⊆ s) :
    (∑ v ∈ s, if v ∈ A then f v else 0) = ∑ v ∈ A, f v := by
  symm
  calc
    (∑ v ∈ A, f v) = ∑ v ∈ A, if v ∈ A then f v else 0 :=
      sum_congr rfl (fun v hv => by simp [hv])
    _ = ∑ v ∈ s, if v ∈ A then f v else 0 :=
      sum_subset hAs (fun v hv hnot => by simp [hnot])

/-- A threshold separates selected weights from all remaining weights. -/
theorem threshold_bound (s A : Finset V) (w x : V → ℝ) (a : ℝ)
    (hAs : A ⊆ s) (hx : ∀ v ∈ s, 0 ≤ x v ∧ x v ≤ 1)
    (hlo : ∀ v ∈ A, w v ≤ a) (hhi : ∀ v ∈ s, v ∉ A → a ≤ w v) :
    (∑ v ∈ A, w v) + a*((∑ v ∈ s, x v) - A.card) ≤ ∑ v ∈ s, w v*x v := by
  have hp : ∀ v ∈ s,
      (if v ∈ A then w v else 0) + a*(x v-(if v ∈ A then 1 else 0)) ≤ w v*x v := by
    intro v hv
    by_cases hA : v ∈ A
    · simp only [if_pos hA]
      nlinarith [mul_nonneg (sub_nonneg.mpr (hlo v hA)) (sub_nonneg.mpr (hx v hv).2)]
    · simp only [if_neg hA, sub_zero, zero_add]
      exact mul_le_mul_of_nonneg_right (hhi v hv hA) (hx v hv).1
  have hs := sum_le_sum hp
  have hw := sum_if_mem_subset A s w hAs
  have hone : (∑ v ∈ s, if v ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by
    rw [sum_if_mem_subset A s (fun _ => (1 : ℝ)) hAs]
    simp
  simpa only [sum_add_distrib, ← mul_sum, sum_sub_distrib, hw, hone] using hs

/-- Round a fractional half-set without increasing any prescribed linear cost. -/
theorem balanced_round (s : Finset V) (w x : V → ℝ)
    (hx : ∀ v ∈ s, 0 ≤ x v ∧ x v ≤ 1) (hmass : (∑ v ∈ s, x v) = (s.card : ℝ)/2) :
    ∃ A ⊆ s, (A.card = s.card/2 ∨ A.card = (s.card+1)/2) ∧
      (∑ v ∈ A, w v) ≤ ∑ v ∈ s, w v*x v := by
  classical
  by_cases hz : s = ∅
  · subst s
    exact ⟨∅, subset_refl _, Or.inl (by simp), by simp⟩
  have hpos : 0 < s.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hz)
  obtain ⟨A,hAs,hAc,horder⟩ := real_ordered_subset w (s.card/2) s (by omega)
  have hD : (s \ A).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff_of_subset hAs, hAc]
    omega
  obtain ⟨b,hb,hmin⟩ := exists_min_image (s \ A) w hD
  have hbs : b ∈ s := (mem_sdiff.mp hb).1
  have hbA : b ∉ A := (mem_sdiff.mp hb).2
  have hbound := threshold_bound s A w x (w b) hAs hx
    (fun v hv => horder v hv b hbs hbA)
    (fun v hv hnot => hmin v (mem_sdiff.mpr ⟨hv,hnot⟩))
  rw [hmass] at hbound
  by_cases heven : s.card = 2*A.card
  · have hevenR : (s.card : ℝ) = 2*(A.card : ℝ) := by exact_mod_cast heven
    have hd : (s.card : ℝ)/2 - A.card = 0 := by linarith
    rw [hd, mul_zero, add_zero] at hbound
    exact ⟨A,hAs,Or.inl hAc,hbound⟩
  · have hodd : s.card = 2*A.card+1 := by omega
    have hoddR : (s.card : ℝ) = 2*(A.card : ℝ)+1 := by exact_mod_cast hodd
    have hd : (s.card : ℝ)/2 - A.card = 1/2 := by linarith
    rw [hd] at hbound
    by_cases hw : 0 ≤ w b
    · exact ⟨A,hAs,Or.inl hAc,by linarith⟩
    · refine ⟨insert b A, (by
        intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · exact hbs
        · exact hAs hv), Or.inr ?_, ?_⟩
      · rw [card_insert_of_notMem hbA]
        omega
      · rw [sum_insert hbA]
        linarith

theorem half_product (k : ℕ) : (k/2)*((k+1)/2) = k^2/4 := by
  let r := k/2
  have hk : k = 2*r ∨ k = 2*r+1 := by omega
  change r*((k+1)/2) = k^2/4
  rcases hk with hk | hk
  · have hc : (k+1)/2 = r := by omega
    rw [hc,hk,show (2*r)^2 = (r*r)*4 by ring]
    omega
  · have hc : (k+1)/2 = r+1 := by omega
    rw [hc,hk,show (2*r+1)^2 = (r*(r+1))*4+1 by ring]
    omega

def coreBudget (k : ℕ) : ℕ := k.choose 2 - k^2/4

theorem balanced_core_cost (k j : ℕ) (hj : j = k/2 ∨ j = (k+1)/2) :
    j.choose 2 + (k-j).choose 2 = coreBudget k := by
  have hjk : j ≤ k := by rcases hj with hj | hj <;> omega
  have hp : j*(k-j) = k^2/4 := by
    rcases hj with rfl | rfl
    · rw [show k-k/2 = (k+1)/2 by omega, half_product]
    · rw [show k-(k+1)/2 = k/2 by omega, Nat.mul_comm, half_product]
  have hcR : ((j.choose 2 + (k-j).choose 2 + j*(k-j) : ℕ) : ℝ) = (k.choose 2 : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_mul, choose_two_real, Nat.cast_sub hjk]
    ring
  have hc : j.choose 2 + (k-j).choose 2 + j*(k-j) = k.choose 2 := by exact_mod_cast hcR
  rw [hp] at hc
  unfold coreBudget
  omega

def indicator (A : Finset V) (v : V) : ℝ := if v ∈ A then 1 else 0

theorem sum_indicator (S A : Finset V) : (∑ v ∈ S, indicator A v) = ((S ∩ A).card : ℝ) := by
  calc
    (∑ v ∈ S, indicator A v) = ∑ v ∈ S, if v ∈ S ∩ A then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro v hv
      simp [indicator,hv]
    _ = ∑ _v ∈ S ∩ A, (1 : ℝ) := sum_if_mem_subset _ _ _ inter_subset_left
    _ = ((S ∩ A).card : ℝ) := by simp

theorem sum_mul_indicator [Fintype V] (w : V → ℝ) (A : Finset V) :
    (∑ v, w v*indicator A v) = ∑ v ∈ A, w v := by
  calc
    (∑ v, w v*indicator A v) = ∑ v, if v ∈ A then w v else 0 := by
      apply sum_congr rfl
      intro v hv
      by_cases h : v ∈ A <;> simp [indicator,h]
    _ = ∑ v ∈ A, w v := sum_if_mem_subset A univ w (subset_univ _)

def fractionalSpokes (S : Finset V) (b : Bool) (x : V → ℝ) : ℝ :=
  if b then ∑ v ∈ S, x v else (S.card : ℝ) - ∑ v ∈ S, x v

theorem spokes_indicator (S A : Finset V) (b : Bool) :
    fractionalSpokes S b (indicator A) = ((side A S b).card : ℝ) := by
  cases b
  · change (S.card : ℝ) - (∑ v ∈ S, indicator A v) = ((S \ A).card : ℝ)
    rw [sum_indicator]
    have hc : ((S \ A).card : ℝ) + (S ∩ A).card = (S.card : ℝ) := by
      exact_mod_cast card_sdiff_add_card_inter S A
    linarith
  · exact sum_indicator S A

def slope (b : Bool) : ℝ := if b then 1 else -1
def offset (S : Finset V) (b : Bool) : ℝ := if b then 0 else S.card

theorem fractionalSpokes_affine (S : Finset V) (b : Bool) (x : V → ℝ) :
    fractionalSpokes S b x = offset S b + slope b*(∑ v ∈ S, x v) := by
  cases b <;> simp [fractionalSpokes,offset,slope] <;> ring

def cutWeight (S T : Finset V) (p q : ℝ) (b d : Bool) (v : V) : ℝ :=
  p*(if v ∈ S then slope b else 0) + q*(if v ∈ T then slope d else 0)

theorem sum_membership [Fintype V] (S : Finset V) (a : ℝ) (x : V → ℝ) :
    (∑ v, (if v ∈ S then a else 0)*x v) = a*(∑ v ∈ S, x v) := by
  calc
    (∑ v, (if v ∈ S then a else 0)*x v) = ∑ v, if v ∈ S then a*x v else 0 := by
      apply sum_congr rfl
      intro v hv
      by_cases h : v ∈ S <;> simp [h]
    _ = ∑ v ∈ S, a*x v := sum_if_mem_subset S univ _ (subset_univ _)
    _ = a*(∑ v ∈ S, x v) := (mul_sum _ _ _).symm

/-- For fixed outer sides, the spoke-deletion cost is an affine function of x. -/
theorem spoke_cost_identity [Fintype V] (S T : Finset V) (p q : ℝ) (b d : Bool) (x : V → ℝ) :
    p*fractionalSpokes S b x + q*fractionalSpokes T d x =
      p*offset S b + q*offset T d + ∑ v, cutWeight S T p q b d v*x v := by
  rw [fractionalSpokes_affine,fractionalSpokes_affine]
  simp only [cutWeight,add_mul,mul_assoc,sum_add_distrib,← mul_sum,sum_membership]
  ring

/-- A balanced graph cover whose cost does not exceed the fractional spoke budget. -/
theorem balanced_cut_witness [Fintype V] (S T : Finset V) (p q : ℕ) (b d : Bool)
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v ∧ x v ≤ 1)
    (hmass : (∑ v, x v) = (Fintype.card V : ℝ)/2) :
    ∃ A : Finset V,
      (A.card = (Fintype.card V)/2 ∨ A.card = ((Fintype.card V)+1)/2) ∧
      ∃ F, IsCover (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) F ∧
        F.card = coreBudget (Fintype.card V) + p*(side A S b).card + q*(side A T d).card ∧
        (F.card : ℝ) ≤ (coreBudget (Fintype.card V) : ℝ) +
          p*fractionalSpokes S b x + q*fractionalSpokes T d x := by
  classical
  let w := cutWeight S T (p : ℝ) (q : ℝ) b d
  obtain ⟨A,hA,hbal,hcost⟩ := balanced_round univ w x (fun v _ => hx v) (by simpa using hmass)
  have hbal' : A.card = (Fintype.card V)/2 ∨ A.card = ((Fintype.card V)+1)/2 := by
    simpa using hbal
  have hspoke : (p : ℝ)*(side A S b).card + (q : ℝ)*(side A T d).card ≤
      p*fractionalSpokes S b x + q*fractionalSpokes T d x := by
    have ha := spoke_cost_identity S T (p : ℝ) (q : ℝ) b d (indicator A)
    rw [spokes_indicator,spokes_indicator,sum_mul_indicator] at ha
    have hf := spoke_cost_identity S T (p : ℝ) (q : ℝ) b d x
    change (∑ v ∈ A, cutWeight S T (p : ℝ) (q : ℝ) b d v) ≤
      ∑ v, cutWeight S T (p : ℝ) (q : ℝ) b d v*x v at hcost
    linarith only [ha,hf,hcost]
  let N : Fin p ⊕ Fin q → Finset V := neighborhood S T
  let sides : Fin p ⊕ Fin q → Bool := Sum.elim (fun _ => b) (fun _ => d)
  obtain ⟨F,hF,hFc⟩ := explicit_cut A N sides
  have hcover : IsCover (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) F := by
    simpa only [N,splitGraph_twoAttached] using hF
  have hc : F.card = A.card.choose 2 + (Fintype.card V-A.card).choose 2 +
      p*(side A S b).card + q*(side A T d).card := by
    simpa [N,sides,neighborhood,Fintype.sum_sum_type,Nat.add_assoc] using hFc
  rw [balanced_core_cost _ _ hbal'] at hc
  refine ⟨A,hbal',F,hcover,hc,?_⟩
  have hcR : (F.card : ℝ) = (coreBudget (Fintype.card V) : ℝ) +
      (p : ℝ)*(side A S b).card + (q : ℝ)*(side A T d).card := by exact_mod_cast hc
  linarith only [hcR,hspoke]

theorem balanced_cover_bound [Fintype V] (S T : Finset V) (p q : ℕ) (b d : Bool)
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v ∧ x v ≤ 1)
    (hmass : (∑ v, x v) = (Fintype.card V : ℝ)/2) :
    (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) ≤
      (coreBudget (Fintype.card V) : ℝ) + p*fractionalSpokes S b x + q*fractionalSpokes T d x := by
  obtain ⟨A,hA,F,hF,hc,hbound⟩ := balanced_cut_witness S T p q b d x hx hmass
  have hmin : coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤ F.card :=
    coverNumber_le_of_budget ⟨F,hF,le_rfl⟩
  exact (show (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) ≤
    (F.card : ℝ) by exact_mod_cast hmin).trans hbound

#print axioms real_ordered_subset
#print axioms threshold_bound
#print axioms balanced_round
#print axioms half_product
#print axioms balanced_core_cost
#print axioms spokes_indicator
#print axioms spoke_cost_identity
#print axioms balanced_cut_witness
#print axioms balanced_cover_bound
#check balanced_cover_bound
end TuzaBalancedRounding

/-!
A direct packing bound from sums of vertex labels.
All triangles of an n-vertex graph split into n edge-disjoint families;
one family has at least a 1/n share of all triangles. No permutations
or probabilistic averaging are required.
OpenAI Codex (GPT-6 Astra), 2026-10-07.
-/

open Finset

namespace TuzaSumColoring

variable {V G : Type*} [DecidableEq V] [AddCommGroup G]

theorem equal_of_shared_edge_and_sum (label : V → G)
    (hinj : Function.Injective label) {t u e : Finset V}
    (ht : t.card = 3) (hu : u.card = 3)
    (he : e.card = 2) (het : e ⊆ t) (heu : e ⊆ u)
    (hsum : ∑ v ∈ t, label v = ∑ v ∈ u, label v) : t = u := by
  have htc : (t \ e).card = 1 := by rw [card_sdiff_of_subset het, ht, he]
  have huc : (u \ e).card = 1 := by rw [card_sdiff_of_subset heu, hu, he]
  obtain ⟨c, hc⟩ := card_eq_one.mp htc
  obtain ⟨d, hd⟩ := card_eq_one.mp huc
  have hcnot : c ∉ e := (mem_sdiff.mp (show c ∈ t \ e by rw [hc]; simp)).2
  have hdnot : d ∉ e := (mem_sdiff.mp (show d ∈ u \ e by rw [hd]; simp)).2
  have hteq : t = insert c e := by
    calc t = (t \ e) ∪ e := (sdiff_union_of_subset het).symm
         _ = insert c e := by rw [hc]; simp
  have hueq : u = insert d e := by
    calc u = (u \ e) ∪ e := (sdiff_union_of_subset heu).symm
         _ = insert d e := by rw [hd]; simp
  rw [hteq, hueq, sum_insert hcnot, sum_insert hdnot] at hsum
  have hcd : c = d := hinj (add_right_cancel hsum)
  rw [hteq, hueq, hcd]

theorem color_class_disjoint [DecidableEq G]
    (A : Finset (Finset V)) (hA : ∀ t ∈ A, t.card = 3)
    (label : V → G) (hinj : Function.Injective label) (c : G) :
    ((A.filter (fun t => ∑ v ∈ t, label v = c)) : Set (Finset V)).PairwiseDisjoint
      (fun t => t.powersetCard 2) := by
  intro t ht u hu hne
  obtain ⟨htA, htc⟩ := mem_filter.mp ht
  obtain ⟨huA, huc⟩ := mem_filter.mp hu
  apply Finset.disjoint_left.mpr
  intro e het heu
  obtain ⟨het', he⟩ := mem_powersetCard.mp het
  obtain ⟨heu', _⟩ := mem_powersetCard.mp heu
  exact hne (equal_of_shared_edge_and_sum label hinj (hA t htA) (hA u huA)
    he het' heu' (htc.trans huc.symm))

theorem packing_of_labeling [Fintype G] [DecidableEq G]
    (A : Finset (Finset V)) (hA : ∀ t ∈ A, t.card = 3)
    (label : V → G) (hinj : Function.Injective label) :
    ∃ P ⊆ A, (P : Set (Finset V)).PairwiseDisjoint (fun t => t.powersetCard 2) ∧
      A.card ≤ Fintype.card G * P.card := by
  let size := fun c : G => (A.filter (fun t => ∑ v ∈ t, label v = c)).card
  obtain ⟨c, _, hmax⟩ := exists_max_image univ size univ_nonempty
  have htotal : A.card = ∑ c : G, size c := by
    exact card_eq_sum_card_fiberwise (s := A) (t := univ)
      (f := fun t => ∑ v ∈ t, label v) (by intro t ht; simp)
  refine ⟨A.filter (fun t => ∑ v ∈ t, label v = c), filter_subset _ _,
    color_class_disjoint A hA label hinj c, ?_⟩
  calc
    A.card = ∑ d : G, size d := htotal
    _ ≤ ∑ d : G, size c := sum_le_sum (fun d hd => hmax d hd)
    _ = Fintype.card G * (A.filter (fun t => ∑ v ∈ t, label v = c)).card := by
      simp [size, mul_comm]

/-- Any family of triples on n vertices has an edge-disjoint subfamily
containing at least a 1/n share, expressed without division. -/
theorem family_packing [Fintype V]
    (A : Finset (Finset V)) (hA : ∀ t ∈ A, t.card = 3) :
    ∃ P ⊆ A, (P : Set (Finset V)).PairwiseDisjoint (fun t => t.powersetCard 2) ∧
      A.card ≤ Fintype.card V * P.card := by
  classical
  by_cases hzero : Fintype.card V = 0
  · have hempty : A = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      have hle := Finset.card_le_univ t
      rw [hA t ht, hzero] at hle
      omega
    refine ⟨∅, empty_subset A, ?_, ?_⟩
    · simp
    · simp [hempty]
  · letI : NeZero (Fintype.card V) := ⟨hzero⟩
    let label : V ≃ ZMod (Fintype.card V) := Fintype.equivOfCardEq (by simp)
    obtain ⟨P, hsub, hdisj, hbound⟩ := packing_of_labeling A hA label label.injective
    exact ⟨P, hsub, hdisj, by simpa using hbound⟩

/-- Every finite simple graph H has an edge-disjoint triangle family P
with t(H) <= |V(H)| * |P|. The empty graph is included. -/
theorem graph_triangle_packing [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∃ P : Finset (Finset V),
      (∀ t ∈ P, H.IsNClique 3 t) ∧
      (P : Set (Finset V)).PairwiseDisjoint (fun t => t.powersetCard 2) ∧
      (H.cliqueFinset 3).card ≤ Fintype.card V * P.card := by
  obtain ⟨P, hsub, hdisj, hbound⟩ := family_packing (H.cliqueFinset 3)
    (fun t ht => (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq)
  refine ⟨P, ?_, hdisj, hbound⟩
  intro t ht
  exact SimpleGraph.mem_cliqueFinset_iff.mp (hsub ht)

/-- The same coloring also supplies the complete-graph packing bound. -/
theorem clique_packing_via_colors [Fintype V] :
    ∃ P : Finset (Finset V),
      (∀ t ∈ P, t.card = 3) ∧
      (P : Set (Finset V)).PairwiseDisjoint (fun t => t.powersetCard 2) ∧
      (Fintype.card V).choose 3 ≤ Fintype.card V * P.card := by
  obtain ⟨P, hsub, hdisj, hbound⟩ := family_packing ((univ : Finset V).powersetCard 3)
    (fun t ht => (mem_powersetCard.mp ht).2)
  refine ⟨P, ?_, hdisj, ?_⟩
  · intro t ht
    exact (mem_powersetCard.mp (hsub ht)).2
  · simpa using hbound

#print axioms graph_triangle_packing
#print axioms family_packing
#print axioms clique_packing_via_colors
#check graph_triangle_packing

end TuzaSumColoring

/-! Exact triangle-family counts and sum-coloring graph bounds. -/
namespace TuzaGraphBounds
open Finset TuzaCompression TuzaGraphCompression TuzaCoverCompression
  TuzaIndependentAllocation TuzaSumColoring
variable {V W C D : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq C] [DecidableEq D]

theorem packingNumber_map_le [Fintype V] [Fintype W] (H : SimpleGraph V) (K : SimpleGraph W)
    (f : V → W) (hf : Function.Injective f) (hadj : ∀ a b, H.Adj a b → K.Adj (f a) (f b)) :
    packingNumber H ≤ packingNumber K := by
  obtain ⟨P,hP,hPc,hmax⟩ := packingNumber_spec H
  obtain ⟨Q,hQ,hQc⟩ := map_packing f hf hadj hP
  obtain ⟨R,hR,hRc,hbound⟩ := packingNumber_spec K
  have hh := hbound Q hQ
  rwa [hQc,hPc] at hh

def centeredFamily [Fintype C] [Fintype D] (S T : Finset V) : Finset (Finset (V ⊕ (C ⊕ D))) :=
  univ.biUnion (fun c : C ⊕ D => ((neighborhood S T c).powersetCard 2).image (cone (fun _ => c)))

theorem centeredFamily_card [Fintype C] [Fintype D] (S T : Finset V) :
    (centeredFamily (C := C) (D := D) S T).card =
      Fintype.card C*S.card.choose 2 + Fintype.card D*T.card.choose 2 := by
  unfold centeredFamily
  rw [card_biUnion]
  · have hh : ∀ c : C ⊕ D, (((neighborhood S T c).powersetCard 2).image (cone (fun _ => c))).card =
        (neighborhood S T c).card.choose 2 := by
      intro c
      rw [card_image_of_injective _ (cone_injective _),card_powersetCard]
    simp only [hh]
    simp [Fintype.sum_sum_type,neighborhood]
  · intro c hc d hd hcd
    apply disjoint_left.mpr
    intro t ht hu
    obtain ⟨e,he,het⟩ := mem_image.mp ht
    obtain ⟨f,hf,hft⟩ := mem_image.mp hu
    have hh : Sum.inr c ∈ cone (fun _ => d) f := by
      rw [hft,← het]
      simp
    exact hcd (inr_mem_cone.mp hh)

def triangleFamily [Fintype V] [Fintype C] [Fintype D] (S T : Finset V) :
    Finset (Finset (V ⊕ (C ⊕ D))) :=
  (univ.powersetCard 3).image lift ∪ centeredFamily S T

theorem triangleFamily_card [Fintype V] [Fintype C] [Fintype D] (S T : Finset V) :
    (triangleFamily (C := C) (D := D) S T).card =
      (Fintype.card V).choose 3 + Fintype.card C*S.card.choose 2 + Fintype.card D*T.card.choose 2 := by
  have hd : Disjoint ((univ.powersetCard 3).image (lift (V := V) (C := C ⊕ D)))
      (centeredFamily S T) := by
    apply disjoint_left.mpr
    intro t ht hu
    obtain ⟨e,he,rfl⟩ := mem_image.mp ht
    obtain ⟨c,hc,hce⟩ := mem_biUnion.mp hu
    obtain ⟨f,hf,hfe⟩ := mem_image.mp hce
    have hh : Sum.inr c ∈ lift e := by rw [← hfe]; simp
    exact inr_not_mem_lift hh
  rw [triangleFamily,card_union_of_disjoint hd,card_image_of_injective _ lift_injective,
    card_powersetCard,card_univ,centeredFamily_card]
  omega

theorem triangleFamily_valid [Fintype V] [Fintype C] [Fintype D] (S T : Finset V) :
    ∀ t ∈ triangleFamily (C := C) (D := D) S T,
      (twoAttached (⊤ : SimpleGraph V) S T C D).IsNClique 3 t := by
  intro t ht
  rcases mem_union.mp ht with ht | ht
  · obtain ⟨e,he,rfl⟩ := mem_image.mp ht
    exact image_clique Sum.inl Sum.inl_injective
      (H := (⊤ : SimpleGraph V)) (K := twoAttached (⊤ : SimpleGraph V) S T C D)
      (fun _ _ h => h)
      (show (⊤ : SimpleGraph V).IsNClique 3 e from
        ⟨by intro a ha b hb hab; exact hab,(mem_powersetCard.mp he).2⟩)
  · obtain ⟨c,hc,hce⟩ := mem_biUnion.mp ht
    obtain ⟨e,he,rfl⟩ := mem_image.mp hce
    exact cone_two_triangle
      (show (⊤ : SimpleGraph V).IsNClique 2 e from
        ⟨by intro a ha b hb hab; exact hab,(mem_powersetCard.mp he).2⟩)
      (fun _ => c) (mem_powersetCard.mp he).1

/-- Direct sum-coloring bound using the exact explicit triangle-family count. -/
theorem triangle_count_bound [Fintype V] [Fintype C] [Fintype D] (S T : Finset V) :
    (Fintype.card V).choose 3 + Fintype.card C*S.card.choose 2 + Fintype.card D*T.card.choose 2 ≤
      (Fintype.card V+Fintype.card C+Fintype.card D)*
        packingNumber (twoAttached (⊤ : SimpleGraph V) S T C D) := by
  let A := triangleFamily (C := C) (D := D) S T
  obtain ⟨P,hPA,hdis,hsize⟩ := family_packing A
    (fun t ht => (triangleFamily_valid S T t ht).card_eq)
  have hP : IsPacking (twoAttached (⊤ : SimpleGraph V) S T C D) P :=
    ⟨fun t ht => triangleFamily_valid S T t (hPA ht),hdis⟩
  obtain ⟨Q,hQ,hQc,hbound⟩ := packingNumber_spec (twoAttached (⊤ : SimpleGraph V) S T C D)
  have hh := hsize.trans (Nat.mul_le_mul_left _ (hbound P hP))
  simpa [A,triangleFamily_card,Fintype.card_sum,Nat.add_assoc] using hh

def twoCenterMap (f : C → C') (g : D → D') : V ⊕ (C ⊕ D) → V ⊕ (C' ⊕ D') :=
  Sum.map id (Sum.map f g)

theorem two_type_monotone [Fintype V] (S T : Finset V) (r z p q : ℕ)
    (hr : r ≤ p) (hz : z ≤ q) :
    packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin r) (Fin z)) ≤
      packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by
  let f : Fin r → Fin p := fun i => ⟨i.val,Nat.lt_of_lt_of_le i.isLt hr⟩
  let g : Fin z → Fin q := fun i => ⟨i.val,Nat.lt_of_lt_of_le i.isLt hz⟩
  have hf : Function.Injective f := by intro a b h; apply Fin.ext; exact congrArg (fun x : Fin p => x.val) h
  have hg : Function.Injective g := by intro a b h; apply Fin.ext; exact congrArg (fun x : Fin q => x.val) h
  apply packingNumber_map_le _ _ (twoCenterMap f g)
  · intro a b h
    cases a with
    | inl a => cases b <;> simpa [twoCenterMap] using h
    | inr a =>
      cases b with
      | inl b => simpa [twoCenterMap] using h
      | inr b => cases a <;> cases b <;> simpa [twoCenterMap,hf.eq_iff,hg.eq_iff] using h
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact hab
      | inr b => cases b <;> exact hab
    | inr a =>
      cases b with
      | inl b => cases a <;> exact hab
      | inr b => exact False.elim hab

theorem subgraph_triangle_bound [Fintype V] (S T : Finset V) (r z p q : ℕ)
    (hr : r ≤ p) (hz : z ≤ q) :
    (Fintype.card V).choose 3 + r*S.card.choose 2 + z*T.card.choose 2 ≤
      (Fintype.card V+r+z)*packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by
  have h := triangle_count_bound (C := Fin r) (D := Fin z) S T
  simp only [Fintype.card_fin] at h
  exact h.trans (Nat.mul_le_mul_left _ (two_type_monotone S T r z p q hr hz))

#print axioms triangleFamily_card
#print axioms triangleFamily_valid
#print axioms triangle_count_bound
#print axioms two_type_monotone
#print axioms subgraph_triangle_bound
#check subgraph_triangle_bound
end TuzaGraphBounds

/-! Real relaxations of the exact allocation bounds. -/
namespace TuzaRealBounds
open Finset TuzaCompression TuzaGraphCompression TuzaIndependentAllocation
  TuzaCoupledAllocation TuzaCoreCompletion TuzaCommonRounding TuzaBalancedRounding
variable {V : Type*} [DecidableEq V] [Fintype V]

theorem rate_mono (a a' b b' c d u : ℝ)
    (ha : 0 ≤ a ∧ a ≤ a' ∧ a' ≤ 1) (hb : 0 ≤ b ∧ b ≤ b' ∧ b' ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ c ∧ u ≤ d) :
    a*c+b*d-a*b*u ≤ a'*c+b'*d-a'*b'*u := by
  have hbU : b*u ≤ u := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-b) hu.1]
  have haU : a'*u ≤ u := by nlinarith [mul_nonneg (sub_nonneg.mpr ha.2.2) hu.1]
  have hp := mul_nonneg (sub_nonneg.mpr ha.2.1) (show 0 ≤ c-b*u by linarith)
  have hq := mul_nonneg (sub_nonneg.mpr hb.2.1) (show 0 ≤ d-a'*u by linarith)
  nlinarith only [hp,hq]

theorem independent_relaxation (s t a b p q c d u L : ℝ)
    (ha : 0 < a ∧ a ≤ s) (hb : 0 < b ∧ b ≤ t)
    (hp : 0 ≤ p ∧ p ≤ a) (hq : 0 ≤ q ∧ q ≤ b)
    (hu : 0 ≤ u ∧ u ≤ c ∧ u ≤ d)
    (hL : b*p*c+a*q*d ≤ a*b*L+p*q*u) :
    p/s*c+q/t*d-(p/s)*(q/t)*u ≤ L := by
  have hs : 0 < s := lt_of_lt_of_le ha.1 ha.2
  have ht : 0 < t := lt_of_lt_of_le hb.1 hb.2
  have hp' : 0 ≤ p/s ∧ p/s ≤ p/a ∧ p/a ≤ 1 := by
    refine ⟨div_nonneg hp.1 hs.le,?_,(div_le_one ha.1).mpr hp.2⟩
    exact (div_le_div_iff₀ hs ha.1).mpr (mul_le_mul_of_nonneg_left ha.2 hp.1)
  have hq' : 0 ≤ q/t ∧ q/t ≤ q/b ∧ q/b ≤ 1 := by
    refine ⟨div_nonneg hq.1 ht.le,?_,(div_le_one hb.1).mpr hq.2⟩
    exact (div_le_div_iff₀ ht hb.1).mpr (mul_le_mul_of_nonneg_left hb.2 hq.1)
  have hm := rate_mono (p/s) (p/a) (q/t) (q/b) c d u hp' hq' hu
  have hid : a*b*(p/a*c+q/b*d-(p/a)*(q/b)*u) = b*p*c+a*q*d-p*q*u := by
    field_simp [ne_of_gt ha.1,ne_of_gt hb.1]
    <;> ring
  have he : p/a*c+q/b*d-(p/a)*(q/b)*u ≤ L := by
    have hn : a*b*(p/a*c+q/b*d-(p/a)*(q/b)*u-L) ≤ 0 := by
      nlinarith only [hid,hL]
    by_contra hnle
    have hp' := mul_pos (mul_pos ha.1 hb.1) (sub_pos.mpr (lt_of_not_ge hnle))
    exact (not_lt_of_ge hn) hp' 
  exact hm.trans he

theorem coupled_relaxation (h t p q c d u L : ℝ)
    (hh : 0 < h ∧ h ≤ t) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hu : 0 ≤ u ∧ u ≤ c ∧ u ≤ d)
    (hL : p*c+q*d ≤ h*L+max 0 (p+q-h)*u) :
    (p*c+q*d-max 0 (p+q-t)*u)/t ≤ L := by
  have ht : 0 < t := lt_of_lt_of_le hh.1 hh.2
  have hA : (p+q)*u ≤ p*c+q*d := by
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hu.2.1),mul_nonneg hq (sub_nonneg.mpr hu.2.2)]
  have hnonneg : 0 ≤ p*c+q*d := by
    have hc : 0 ≤ c := hu.1.trans hu.2.1
    have hd : 0 ≤ d := hu.1.trans hu.2.2
    exact add_nonneg (mul_nonneg hp hc) (mul_nonneg hq hd)
  have hcompare : h*(p*c+q*d-max 0 (p+q-t)*u) ≤
      t*(p*c+q*d-max 0 (p+q-h)*u) := by
    by_cases hmH : p+q ≤ h
    · have hmT : p+q ≤ t := hmH.trans hh.2
      rw [max_eq_left (by linarith : p+q-t ≤ 0),max_eq_left (by linarith : p+q-h ≤ 0)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) hnonneg]
    · by_cases hmT : p+q ≤ t
      · rw [max_eq_left (by linarith : p+q-t ≤ 0),max_eq_right (by linarith : 0 ≤ p+q-h)]
        have h1 := mul_nonneg (sub_nonneg.mpr hh.2) (sub_nonneg.mpr hA)
        have h2 := mul_nonneg (mul_nonneg hh.1.le (by linarith : 0 ≤ t-(p+q))) hu.1
        nlinarith only [h1,h2]
      · rw [max_eq_right (by linarith : 0 ≤ p+q-t),max_eq_right (by linarith : 0 ≤ p+q-h)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (sub_nonneg.mpr hA)]
  apply (div_le_iff₀ ht).mpr
  have hscaled := mul_le_mul_of_nonneg_left hL ht.le
  have hprod : h*(p*c+q*d-max 0 (p+q-t)*u) ≤ h*(L*t) := by
    nlinarith only [hcompare,hscaled]
  by_contra hnle
  have hp' := mul_pos hh.1 (sub_pos.mpr (lt_of_not_ge hnle))
  nlinarith only [hprod,hp']

theorem palette_bounds (s : ℕ) (hs : 2 ≤ s) : 0 < colorCount s ∧ colorCount s ≤ s := by
  unfold colorCount
  split <;> omega

theorem palette_mono (s t : ℕ) (hst : s ≤ t) : colorCount s ≤ colorCount t := by
  unfold colorCount
  split <;> split <;> omega

#print axioms rate_mono
#print axioms independent_relaxation
#print axioms coupled_relaxation
#print axioms palette_bounds
#print axioms palette_mono
end TuzaRealBounds
/-!
Fractional two-neighborhood cuts and the separable cover bound.
OpenAI Codex (GPT-6 Astra), 2026-10-07.
-/
namespace TuzaSeparableCover
open Finset TuzaBalancedRounding TuzaCoverCompression TuzaIndependentAllocation

variable {V : Type*} [DecidableEq V]

theorem ratio_bounds (n m : ℝ) (hn : 0 ≤ n) (hm : 0 ≤ m ∧ m ≤ n) :
    0 ≤ m/n ∧ m/n ≤ 1 := by
  by_cases hz : n = 0
  · simp [hz]
  · exact ⟨div_nonneg hm.1 hn, (div_le_one (lt_of_le_of_ne hn (Ne.symm hz))).mpr hm.2⟩

noncomputable def portion (S : Finset V) (m : ℝ) (v : V) : ℝ :=
  (m/(S.card : ℝ))*indicator S v

theorem portion_zero (S : Finset V) (v : V) : portion S 0 v = 0 := by
  simp [portion]

theorem portion_add (S : Finset V) (a b : ℝ) (v : V) :
    portion S (a+b) v = portion S a v + portion S b v := by
  simp only [portion,add_div,add_mul]

theorem portion_sum (S R : Finset V) (m : ℝ) :
    (∑ v ∈ R, portion S m v) = m/(S.card : ℝ)*((R ∩ S).card : ℝ) := by
  simp only [portion,← mul_sum,sum_indicator]

theorem portion_sum_subset (S R : Finset V) (m : ℝ) (hSR : S ⊆ R)
    (hm : 0 ≤ m ∧ m ≤ (S.card : ℝ)) : (∑ v ∈ R, portion S m v) = m := by
  rw [portion_sum,inter_eq_right.mpr hSR]
  by_cases hz : S.card = 0
  · have hmz : m = 0 := by simp only [hz,Nat.cast_zero] at hm; linarith
    simp [hmz]
  · exact div_mul_cancel₀ _ (by exact_mod_cast hz)

theorem portion_sum_disjoint (S R : Finset V) (m : ℝ)
    (h : ∀ v ∈ R, v ∉ S) : (∑ v ∈ R, portion S m v) = 0 := by
  apply sum_eq_zero
  intro v hv
  simp [portion,indicator,h v hv]

noncomputable def regions (S T : Finset V) (a b c : ℝ) (v : V) : ℝ :=
  portion (S \ T) a v + portion (T \ S) b v + portion (S ∩ T) c v

theorem regions_add (S T : Finset V) (a b c d e f : ℝ) (v : V) :
    regions S T (a+d) (b+e) (c+f) v = regions S T a b c v + regions S T d e f v := by
  simp only [regions,portion_add]
  ring

theorem regions_spec [Fintype V] (S T : Finset V) (a b c : ℝ)
    (ha : 0 ≤ a ∧ a ≤ ((S \ T).card : ℝ))
    (hb : 0 ≤ b ∧ b ≤ ((T \ S).card : ℝ))
    (hc : 0 ≤ c ∧ c ≤ ((S ∩ T).card : ℝ)) :
    (∀ v, 0 ≤ regions S T a b c v ∧ regions S T a b c v ≤ 1) ∧
    (∑ v, regions S T a b c v) = a+b+c ∧
    (∑ v ∈ S, regions S T a b c v) = a+c ∧
    (∑ v ∈ T, regions S T a b c v) = b+c := by
  have hA := ratio_bounds ((S \ T).card : ℝ) a (by positivity) ha
  have hB := ratio_bounds ((T \ S).card : ℝ) b (by positivity) hb
  have hC := ratio_bounds ((S ∩ T).card : ℝ) c (by positivity) hc
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    by_cases hs : v ∈ S <;> by_cases ht : v ∈ T <;>
      simp [regions,portion,indicator,hs,ht,hA,hB,hC]
  · simp only [regions,sum_add_distrib]
    rw [portion_sum_subset _ _ _ (subset_univ _) ha,
      portion_sum_subset _ _ _ (subset_univ _) hb,
      portion_sum_subset _ _ _ (subset_univ _) hc]
  · simp only [regions,sum_add_distrib]
    rw [portion_sum_subset _ _ _ sdiff_subset ha,
      portion_sum_disjoint (T \ S) S b (by intro v hv hh; exact (mem_sdiff.mp hh).2 hv),
      portion_sum_subset _ _ _ inter_subset_left hc]
    ring
  · simp only [regions,sum_add_distrib]
    rw [portion_sum_disjoint (S \ T) T a (by intro v hv hh; exact (mem_sdiff.mp hh).2 hv),
      portion_sum_subset _ _ _ sdiff_subset hb,
      portion_sum_subset _ _ _ inter_subset_right hc]
    ring

/-- Fill between pointwise lower and upper capacities to attain any intermediate mass. -/
theorem fill_between [Fintype V] (l h : V → ℝ) (z : ℝ)
    (hlh : ∀ v, l v ≤ h v) (hz : (∑ v, l v) ≤ z ∧ z ≤ ∑ v, h v) :
    ∃ x : V → ℝ, (∀ v, l v ≤ x v ∧ x v ≤ h v) ∧ (∑ v, x v) = z := by
  let L := ∑ v, l v
  let H := ∑ v, h v
  have hLH : L ≤ H := sum_le_sum (fun v _ => hlh v)
  by_cases he : H = L
  · refine ⟨l, fun v => ⟨le_rfl,hlh v⟩, ?_⟩
    change L = z
    change L ≤ z ∧ z ≤ H at hz
    linarith
  · have hd : 0 < H-L := sub_pos.mpr (lt_of_le_of_ne hLH (Ne.symm he))
    let a := (z-L)/(H-L)
    have ha : 0 ≤ a ∧ a ≤ 1 := ratio_bounds (H-L) (z-L) hd.le (by
      change L ≤ z ∧ z ≤ H at hz
      constructor <;> linarith)
    refine ⟨fun v => l v+a*(h v-l v),?_,?_⟩
    · intro v
      have hp := mul_nonneg ha.1 (sub_nonneg.mpr (hlh v))
      have hq := mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr (hlh v))
      constructor <;> nlinarith
    · simp only [sum_add_distrib,← mul_sum,sum_sub_distrib]
      change L+a*(H-L) = z
      have heq : a*(H-L) = z-L := div_mul_cancel₀ _ (ne_of_gt hd)
      linarith

/-- Opposite retained sides: the two common demands fit into their intersection. -/
theorem opposite_masses (s t u bs bt : ℝ)
    (hu : 0 ≤ u ∧ u ≤ s ∧ u ≤ t) (hs : 0 ≤ bs ∧ bs ≤ s)
    (ht : 0 ≤ bt ∧ bt ≤ t) (hfit : u ≤ bs+bt) :
    ∃ a b c d : ℝ,
      (0 ≤ a ∧ a ≤ s-u) ∧ (0 ≤ b ∧ b ≤ t-u) ∧
      (0 ≤ c ∧ c ≤ u) ∧ (0 ≤ d ∧ d ≤ u) ∧
      c+d ≤ u ∧ a+c = s-bs ∧ b+d = t-bt := by
  refine ⟨s-bs-max 0 (u-bs),t-bt-max 0 (u-bt),max 0 (u-bs),max 0 (u-bt),?_⟩
  simp only [max_def]
  split_ifs <;> (repeat' constructor) <;> linarith

/-- Same retained side: maximize overlap before using either exclusive region. -/
theorem same_masses (s t u rs rt z : ℝ)
    (hu : 0 ≤ u ∧ u ≤ s ∧ u ≤ t) (hs : 0 ≤ rs ∧ rs ≤ s ∧ rs ≤ z)
    (ht : 0 ≤ rt ∧ rt ≤ t ∧ rt ≤ z) (hfit : rs+rt-u ≤ z) :
    ∃ a b c : ℝ,
      (0 ≤ a ∧ a ≤ s-u) ∧ (0 ≤ b ∧ b ≤ t-u) ∧
      (0 ≤ c ∧ c ≤ u) ∧ a+b+c ≤ z ∧ rs ≤ a+c ∧ rt ≤ b+c := by
  refine ⟨max 0 (rs-u),max 0 (rt-u),min u (max rs rt),?_⟩
  simp only [min_def,max_def]
  split_ifs <;> (repeat' constructor) <;> linarith

theorem region_sizes [Fintype V] (S T : Finset V) :
    ((S \ T).card : ℝ) = (S.card : ℝ)-(S ∩ T).card ∧
    ((T \ S).card : ℝ) = (T.card : ℝ)-(S ∩ T).card := by
  have hs : ((S \ T).card : ℝ)+(S ∩ T).card = (S.card : ℝ) := by
    exact_mod_cast card_sdiff_add_card_inter S T
  have ht : ((T \ S).card : ℝ)+(S ∩ T).card = (T.card : ℝ) := by
    rw [inter_comm S T]
    exact_mod_cast card_sdiff_add_card_inter T S
  constructor <;> linarith

theorem fractional_cut [Fintype V] (S T : Finset V) (bs bt : ℝ)
    (hs : 0 ≤ bs ∧ bs ≤ (S.card : ℝ))
    (ht : 0 ≤ bt ∧ bt ≤ (T.card : ℝ))
    (hrs : (S.card : ℝ)-bs ≤ (Fintype.card V : ℝ)/2)
    (hrt : (T.card : ℝ)-bt ≤ (Fintype.card V : ℝ)/2)
    (hgap : (S.card : ℝ)+(T.card : ℝ)-(Fintype.card V : ℝ)/2 ≤ 2*(bs+bt)) :
    ∃ (x : V → ℝ) (b d : Bool),
      (∀ v, 0 ≤ x v ∧ x v ≤ 1) ∧ (∑ v, x v) = (Fintype.card V : ℝ)/2 ∧
      fractionalSpokes S b x ≤ bs ∧ fractionalSpokes T d x ≤ bt := by
  let s : ℝ := S.card
  let t : ℝ := T.card
  let u : ℝ := (S ∩ T).card
  let k : ℝ := Fintype.card V
  have hu : 0 ≤ u ∧ u ≤ s ∧ u ≤ t := by
    refine ⟨by positivity,?_,?_⟩
    · change ((S ∩ T).card : ℝ) ≤ (S.card : ℝ)
      exact_mod_cast card_le_card (inter_subset_left : S ∩ T ⊆ S)
    · change ((S ∩ T).card : ℝ) ≤ (T.card : ℝ)
      exact_mod_cast card_le_card (inter_subset_right : S ∩ T ⊆ T)
  have hsize := region_sizes S T
  by_cases hop : u ≤ bs+bt
  · obtain ⟨a,b,c,d,ha,hb,hc,hd,hcd,has,hbt⟩ := opposite_masses s t u bs bt hu hs ht hop
    have ha' : 0 ≤ a ∧ a ≤ ((S \ T).card : ℝ) := by rw [hsize.1]; exact ha
    have hb' : 0 ≤ b ∧ b ≤ ((T \ S).card : ℝ) := by rw [hsize.2]; exact hb
    have hc' : 0 ≤ c ∧ c ≤ ((S ∩ T).card : ℝ) := hc
    have hd' : 0 ≤ d ∧ d ≤ ((S ∩ T).card : ℝ) := hd
    have hzS : 0 ≤ (0 : ℝ) ∧ 0 ≤ ((S \ T).card : ℝ) := ⟨le_rfl,by positivity⟩
    have hzT : 0 ≤ (0 : ℝ) ∧ 0 ≤ ((T \ S).card : ℝ) := ⟨le_rfl,by positivity⟩
    let l := regions S T a 0 c
    let g := regions S T 0 b d
    have hl := regions_spec S T a 0 c ha' hzT hc'
    have hg := regions_spec S T 0 b d hzS hb' hd'
    have hsum := regions_spec S T a b (c+d) ha' hb' ⟨add_nonneg hc.1 hd.1,hcd⟩
    have hlg : ∀ v, l v ≤ 1-g v := by
      intro v
      have hh := (hsum.1 v).2
      have he : regions S T a b (c+d) v = l v+g v := by
        simpa [l,g] using regions_add S T a 0 c 0 b d v
      rw [he] at hh
      linarith
    have hL : (∑ v, l v) = s-bs := by simpa [l,has] using hl.2.1
    have hG : (∑ v, g v) = t-bt := by simpa [g,hbt] using hg.2.1
    have hH : (∑ v : V, (1 - g v)) = k-(t-bt) := by simp [sum_sub_distrib,hG,k]
    obtain ⟨x,hx,hmass⟩ := fill_between l (fun v => 1-g v) (k/2) hlg (by
      rw [hL,hH]
      constructor <;> linarith)
    refine ⟨x,false,true,?_,hmass,?_,?_⟩
    · intro v
      exact ⟨(hl.1 v).1.trans (hx v).1, (hx v).2.trans (by linarith [(hg.1 v).1])⟩
    · have hh := sum_le_sum (s := S) (fun v _ => (hx v).1)
      have he : (∑ v ∈ S, l v) = s-bs := by simpa [l,has] using hl.2.2.1
      change (S.card : ℝ)-(∑ v ∈ S, x v) ≤ bs
      rw [he] at hh
      linarith
    · have hh := sum_le_sum (s := T) (fun v _ => (hx v).2)
      have he : (∑ v ∈ T, g v) = t-bt := by simpa [g,hbt] using hg.2.2.2
      have hh' : (∑ v ∈ T, (1 - g v)) = bt := by
        simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one,he]
        change t-(t-bt) = bt
        ring
      change (∑ v ∈ T, x v) ≤ bt
      rwa [hh'] at hh
  · have hfit : (s-bs)+(t-bt)-u ≤ k/2 := by change s+t-k/2 ≤ 2*(bs+bt) at hgap; linarith
    obtain ⟨a,b,c,ha,hb,hc,habc,has,hbt⟩ := same_masses s t u (s-bs) (t-bt) (k/2)
      hu ⟨by linarith [hs.2],by linarith [hs.1],hrs⟩
      ⟨by linarith [ht.2],by linarith [ht.1],hrt⟩ hfit
    have ha' : 0 ≤ a ∧ a ≤ ((S \ T).card : ℝ) := by rw [hsize.1]; exact ha
    have hb' : 0 ≤ b ∧ b ≤ ((T \ S).card : ℝ) := by rw [hsize.2]; exact hb
    have hr := regions_spec S T a b c ha' hb' hc
    let l := regions S T a b c
    obtain ⟨x,hx,hmass⟩ := fill_between l (fun _ => 1) (k/2) (fun v => (hr.1 v).2) (by
      constructor
      · exact hr.2.1.le.trans habc
      · simp only [sum_const,nsmul_eq_mul,mul_one,card_univ]
        change k/2 ≤ k
        have : 0 ≤ k := by positivity
        linarith)
    refine ⟨x,false,false,?_,hmass,?_,?_⟩
    · intro v
      exact ⟨(hr.1 v).1.trans (hx v).1,(hx v).2⟩
    · have hh := sum_le_sum (s := S) (fun v _ => (hx v).1)
      change (S.card : ℝ)-(∑ v ∈ S, x v) ≤ bs
      change (∑ v ∈ S, regions S T a b c v) ≤ _ at hh
      rw [hr.2.2.1] at hh
      linarith
    · have hh := sum_le_sum (s := T) (fun v _ => (hx v).1)
      change (T.card : ℝ)-(∑ v ∈ T, x v) ≤ bt
      change (∑ v ∈ T, regions S T a b c v) ≤ _ at hh
      rw [hr.2.2.2] at hh
      linarith

noncomputable def penalty (k d : ℝ) : ℝ := max 0 (max (d/2-k/8) (d-k/2))

theorem penalty_bounds (k d : ℝ) (hk : 0 ≤ k) (hd : 0 ≤ d ∧ d ≤ k) :
    (0 ≤ penalty k d ∧ penalty k d ≤ d) ∧ d-penalty k d ≤ k/2 := by
  unfold penalty
  simp only [max_def]
  split_ifs <;> (repeat' constructor) <;> linarith

theorem penalty_gap (k s t : ℝ) : s+t-k/2 ≤ 2*(penalty k s+penalty k t) := by
  have hs : s/2-k/8 ≤ penalty k s := (le_max_left _ _).trans (le_max_right _ _)
  have ht : t/2-k/8 ≤ penalty k t := (le_max_left _ _).trans (le_max_right _ _)
  linarith

/-- The full separable bound, with no restriction on overlap or multiplicities. -/
theorem separable_cover_bound [Fintype V] (S T : Finset V) (p q : ℕ) :
    (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) ≤
      (coreBudget (Fintype.card V) : ℝ) +
        p*penalty (Fintype.card V) S.card + q*penalty (Fintype.card V) T.card := by
  have hs := penalty_bounds (Fintype.card V : ℝ) (S.card : ℝ) (by positivity)
    ⟨by positivity,by exact_mod_cast card_le_univ S⟩
  have ht := penalty_bounds (Fintype.card V : ℝ) (T.card : ℝ) (by positivity)
    ⟨by positivity,by exact_mod_cast card_le_univ T⟩
  obtain ⟨x,b,d,hx,hmass,hS,hT⟩ := fractional_cut S T _ _ hs.1 ht.1 hs.2 ht.2
    (penalty_gap _ _ _)
  have hcover := balanced_cover_bound S T p q b d x hx hmass
  have hp := mul_le_mul_of_nonneg_left hS (show (0 : ℝ) ≤ p by positivity)
  have hq := mul_le_mul_of_nonneg_left hT (show (0 : ℝ) ≤ q by positivity)
  linarith

#print axioms regions_spec
#print axioms fill_between
#print axioms opposite_masses
#print axioms same_masses
#print axioms fractional_cut
#print axioms penalty_bounds
#print axioms penalty_gap
#print axioms separable_cover_bound
#check separable_cover_bound
end TuzaSeparableCover

/-! Four-region fractional cuts with prescribed masses. -/
namespace TuzaFractionalOrders
open Finset TuzaSeparableCover TuzaBalancedRounding TuzaCoverCompression
  TuzaIndependentAllocation

variable {V : Type*} [DecidableEq V] [Fintype V]

def outside (S T : Finset V) : Finset V := univ \ (S ∪ T)

noncomputable def fourRegions (S T : Finset V) (a b c d : ℝ) (v : V) : ℝ :=
  regions S T a b c v + portion (outside S T) d v

theorem four_regions_spec (S T : Finset V) (a b c d : ℝ)
    (ha : 0 ≤ a ∧ a ≤ ((S \ T).card : ℝ))
    (hb : 0 ≤ b ∧ b ≤ ((T \ S).card : ℝ))
    (hc : 0 ≤ c ∧ c ≤ ((S ∩ T).card : ℝ))
    (hd : 0 ≤ d ∧ d ≤ ((outside S T).card : ℝ)) :
    (∀ v, 0 ≤ fourRegions S T a b c d v ∧ fourRegions S T a b c d v ≤ 1) ∧
    (∑ v, fourRegions S T a b c d v) = a+b+c+d ∧
    (∑ v ∈ S, fourRegions S T a b c d v) = a+c ∧
    (∑ v ∈ T, fourRegions S T a b c d v) = b+c := by
  have hr := regions_spec S T a b c ha hb hc
  have hd' := ratio_bounds ((outside S T).card : ℝ) d (by positivity) hd
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    by_cases hs : v ∈ S <;> by_cases ht : v ∈ T
    · simpa [fourRegions,portion,indicator,outside,hs,ht] using hr.1 v
    · simpa [fourRegions,portion,indicator,outside,hs,ht] using hr.1 v
    · simpa [fourRegions,portion,indicator,outside,hs,ht] using hr.1 v
    · simpa [fourRegions,regions,portion,indicator,outside,hs,ht] using hd'
  · simp only [fourRegions,sum_add_distrib]
    rw [hr.2.1,portion_sum_subset _ _ _ (subset_univ _) hd]
  · simp only [fourRegions,sum_add_distrib]
    rw [hr.2.2.1,portion_sum_disjoint (outside S T) S d (by
      intro v hv hh; exact (mem_sdiff.mp hh).2 (mem_union_left _ hv)),add_zero]
  · simp only [fourRegions,sum_add_distrib]
    rw [hr.2.2.2,portion_sum_disjoint (outside S T) T d (by
      intro v hv hh; exact (mem_sdiff.mp hh).2 (mem_union_right _ hv)),add_zero]

theorem four_region_cover (S T : Finset V) (p q : ℕ) (a b c d : ℝ) (bs bt : Bool)
    (ha : 0 ≤ a ∧ a ≤ ((S \ T).card : ℝ))
    (hb : 0 ≤ b ∧ b ≤ ((T \ S).card : ℝ))
    (hc : 0 ≤ c ∧ c ≤ ((S ∩ T).card : ℝ))
    (hd : 0 ≤ d ∧ d ≤ ((outside S T).card : ℝ))
    (hm : a+b+c+d = (Fintype.card V : ℝ)/2) :
    (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) ≤
      (coreBudget (Fintype.card V) : ℝ) +
        p*(if bs then a+c else (S.card : ℝ)-a-c) +
        q*(if bt then b+c else (T.card : ℝ)-b-c) := by
  have h := four_regions_spec S T a b c d ha hb hc hd
  have hh := balanced_cover_bound S T p q bs bt (fourRegions S T a b c d) h.1 (h.2.1.trans hm)
  simp only [fractionalSpokes,h.2.2.1,h.2.2.2] at hh
  simpa only [sub_add_eq_sub_sub] using hh

/-- Greedy filling of four nonnegative capacities to any feasible total. -/
theorem greedy_four (a b c d z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hz : 0 ≤ z ∧ z ≤ a+b+c+d) :
    let r := min a z
    let s := min b (z-r)
    let t := min c (z-r-s)
    (0 ≤ r ∧ r ≤ a) ∧ (0 ≤ s ∧ s ≤ b) ∧ (0 ≤ t ∧ t ≤ c) ∧
      (0 ≤ z-r-s-t ∧ z-r-s-t ≤ d) := by
  dsimp
  simp only [min_def]
  split_ifs <;> (repeat' constructor) <;> linarith

#print axioms four_regions_spec
#print axioms four_region_cover
#print axioms greedy_four
end TuzaFractionalOrders
/-! Core-only covers outside the neighborhood shadow. -/
namespace TuzaShadowCovers
open Finset TuzaCompression TuzaGraphCompression TuzaCoverCompression TuzaCutCovers
  TuzaCoreCompletion TuzaIndependentAllocation

variable {V C : Type*} [DecidableEq V] [DecidableEq C]

def pairOf (p : V × V) : Finset V := {p.1,p.2}

theorem pairOf_injOn (L R : Finset V) (hd : Disjoint L R) :
    Set.InjOn (pairOf (V := V)) (L.product R) := by
  intro p hp q hq he
  have hp' := mem_product.mp hp
  have hq' := mem_product.mp hq
  have ha : p.1 = q.1 ∨ p.1 = q.2 := by
    have hh : p.1 ∈ pairOf p := by simp [pairOf]
    rw [he] at hh
    simpa [pairOf] using hh
  have hb : p.2 = q.1 ∨ p.2 = q.2 := by
    have hh : p.2 ∈ pairOf p := by simp [pairOf]
    rw [he] at hh
    simpa [pairOf] using hh
  have ha' : p.1 = q.1 := ha.resolve_right (fun h =>
    disjoint_left.mp hd hp'.1 (h.symm ▸ hq'.2))
  have hb' : p.2 = q.2 := hb.resolve_left (fun h =>
    disjoint_left.mp hd (h.symm ▸ hq'.1) hp'.2)
  exact Prod.ext ha' hb'

theorem lifted_core_cover [Fintype V] (N : C → Finset V) (E : Finset (Finset V))
    (hE : IsCover (⊤ : SimpleGraph V) E)
    (hN : ∀ c, (N c).powersetCard 2 ⊆ E) :
    IsCover (splitGraph N) (E.image (lift (C := C))) := by
  refine ⟨?_,?_⟩
  · intro e he
    obtain ⟨d,hd,rfl⟩ := mem_image.mp he
    exact image_clique Sum.inl Sum.inl_injective
      (H := (⊤ : SimpleGraph V)) (K := splitGraph N) (fun _ _ h => h) (hE.1 d hd)
  · intro t ht
    by_cases hout : t.toRight.Nonempty
    · obtain ⟨c,hc⟩ := hout
      have htc := centered_left_card (splitGraph N) (fun _ _ h => h) ht ⟨c,hc⟩
      have hsub : t.toLeft ⊆ N c := by
        intro v hv
        exact ht.isClique (mem_toLeft.mp hv) (mem_toRight.mp hc) (by simp)
      exact ⟨lift t.toLeft, mem_image.mpr ⟨t.toLeft,hN c (mem_powersetCard.mpr ⟨hsub,htc⟩),rfl⟩,
        lift_subset_of_left (subset_refl _)⟩
    · have hr : t.toRight.card = 0 := by
        have he : t.toRight = ∅ := not_nonempty_iff_eq_empty.mp hout
        simp [he]
      have hc := card_toLeft_add_card_toRight (u := t)
      have htcard := ht.card_eq
      have hleft : (⊤ : SimpleGraph V).IsNClique 3 t.toLeft :=
        ⟨by intro a ha b hb hab; exact hab,by omega⟩
      obtain ⟨e,he,het⟩ := hE.2 _ hleft
      exact ⟨lift e,mem_image.mpr ⟨e,he,rfl⟩,lift_subset_of_left het⟩

def crossProduct (L R S : Finset V) : Finset (V × V) := (L ∩ S).product (R ∩ S)

def retained [Fintype V] (A S T : Finset V) : Finset (V × V) :=
  A.product (univ \ A) \ (crossProduct A (univ \ A) S ∪ crossProduct A (univ \ A) T)

def shadowCore [Fintype V] (A S T : Finset V) : Finset (Finset V) :=
  univ.powersetCard 2 \ (retained A S T).image pairOf

theorem retained_subset [Fintype V] (A S T : Finset V) :
    retained A S T ⊆ A.product (univ \ A) := sdiff_subset

theorem retained_edges [Fintype V] (A S T : Finset V) :
    (retained A S T).image pairOf ⊆ univ.powersetCard 2 := by
  intro e he
  obtain ⟨p,hp,rfl⟩ := mem_image.mp he
  have hh := mem_product.mp (retained_subset A S T hp)
  apply mem_powersetCard.mpr
  refine ⟨subset_univ _,card_pair ?_⟩
  intro heq
  exact (mem_sdiff.mp hh.2).2 (heq ▸ hh.1)

theorem coreEdges_subset_shadow [Fintype V] (A S T : Finset V) :
    coreEdges A ⊆ shadowCore A S T := by
  intro e he
  have hec : e.card = 2 := by
    rcases mem_union.mp he with he | he <;> exact (mem_powersetCard.mp he).2
  refine mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,hec⟩,?_⟩
  intro hr
  obtain ⟨p,hp,hpe⟩ := mem_image.mp hr
  have hp' := mem_product.mp (retained_subset A S T hp)
  have hpa : p.1 ∈ e := by rw [← hpe]; simp [pairOf]
  have hpb : p.2 ∈ e := by rw [← hpe]; simp [pairOf]
  rcases mem_union.mp he with he | he
  · exact (mem_sdiff.mp hp'.2).2 ((mem_powersetCard.mp he).1 hpb)
  · exact (mem_sdiff.mp ((mem_powersetCard.mp he).1 hpa)).2 hp'.1

theorem shadow_neighborhoods [Fintype V] (A S T : Finset V) :
    S.powersetCard 2 ⊆ shadowCore A S T ∧ T.powersetCard 2 ⊆ shadowCore A S T := by
  have step : ∀ W : Finset V, W = S ∨ W = T → W.powersetCard 2 ⊆ shadowCore A S T := by
    intro W hW e he
    obtain ⟨hes,hec⟩ := mem_powersetCard.mp he
    refine mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,hec⟩,?_⟩
    intro hh
    obtain ⟨p,hp,hpe⟩ := mem_image.mp hh
    have hp' := mem_product.mp (retained_subset A S T hp)
    have ha : p.1 ∈ W := hes (by rw [← hpe]; simp [pairOf])
    have hb : p.2 ∈ W := hes (by rw [← hpe]; simp [pairOf])
    have hw : p ∈ crossProduct A (univ \ A) W :=
      mem_product.mpr ⟨mem_inter.mpr ⟨hp'.1,ha⟩,mem_inter.mpr ⟨hp'.2,hb⟩⟩
    apply (mem_sdiff.mp hp).2
    rcases hW with rfl | rfl
    · exact mem_union_left _ hw
    · exact mem_union_right _ hw
  exact ⟨step S (Or.inl rfl),step T (Or.inr rfl)⟩

theorem shadow_isCover [Fintype V] (A S T : Finset V) (p q : ℕ) :
    IsCover (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q))
      ((shadowCore A S T).image (lift (C := Fin p ⊕ Fin q))) := by
  have hE : IsCover (⊤ : SimpleGraph V) (shadowCore A S T) := by
    apply cover_of_same_color (⊤ : SimpleGraph V) (fun v => decide (v ∈ A))
    · intro e he
      exact ⟨by intro a ha b hb hab; exact hab,(mem_powersetCard.mp (mem_sdiff.mp he).1).2⟩
    · intro a b hab hc
      exact coreEdges_subset_shadow A S T (pair_mem_coreEdges A hab hc)
  have hN : ∀ c : Fin p ⊕ Fin q, (neighborhood S T c).powersetCard 2 ⊆ shadowCore A S T := by
    intro c
    cases c
    · exact (shadow_neighborhoods A S T).1
    · exact (shadow_neighborhoods A S T).2
  simpa only [splitGraph_twoAttached] using lifted_core_cover (neighborhood S T) (shadowCore A S T) hE hN

def shadowCost (k a ls rs lt rt lu ru : ℕ) : ℕ :=
  k.choose 2 - (a*(k-a)-(ls*rs+lt*rt-lu*ru))

theorem shadowCore_card [Fintype V] (A S T : Finset V) :
    (shadowCore A S T).card = shadowCost (Fintype.card V) A.card
      (A ∩ S).card ((univ \ A) ∩ S).card
      (A ∩ T).card ((univ \ A) ∩ T).card
      (A ∩ (S ∩ T)).card ((univ \ A) ∩ (S ∩ T)).card := by
  let R : Finset V := univ \ A
  have hd : Disjoint A R := by apply disjoint_left.mpr; intro v hv hr; exact (mem_sdiff.mp hr).2 hv
  have hinj := pairOf_injOn A R hd
  have himage : ((retained A S T).image pairOf).card = (retained A S T).card :=
    card_image_of_injOn (fun x hx y hy h => hinj (retained_subset A S T hx) (retained_subset A S T hy) h)
  have hsub : crossProduct A R S ∪ crossProduct A R T ⊆ A.product R := by
    intro v hv
    rcases mem_union.mp hv with hv | hv <;>
      exact mem_product.mpr ⟨(mem_inter.mp (mem_product.mp hv).1).1,(mem_inter.mp (mem_product.mp hv).2).1⟩
  have hinter : crossProduct A R S ∩ crossProduct A R T = crossProduct A R (S ∩ T) := by
    ext v
    simp [crossProduct,and_assoc,and_left_comm,and_comm]
  have hcount := card_sdiff_add_card_eq_card hsub
  have hunion := card_union_add_card_inter (crossProduct A R S) (crossProduct A R T)
  rw [hinter] at hunion
  simp only [crossProduct,product_eq_sprod,card_product] at hunion
  change (retained A S T).card + _ = _ at hcount
  rw [product_eq_sprod,card_product,show R.card = Fintype.card V-A.card by simp [R,card_sdiff_of_subset (subset_univ A)]] at hcount
  have hall := card_sdiff_add_card_eq_card (retained_edges A S T)
  change (shadowCore A S T).card + _ = _ at hall
  rw [himage,card_powersetCard,card_univ] at hall
  change (crossProduct A R S ∪ crossProduct A R T).card +
    (A ∩ (S ∩ T)).card*(R ∩ (S ∩ T)).card =
    (A ∩ S).card*(R ∩ S).card+(A ∩ T).card*(R ∩ T).card at hunion
  have solveSub (a b c : ℕ) (h : a+b=c) : a=c-b := by omega
  have hU := solveSub _ _ _ hunion
  have hR := solveSub _ _ _ hcount
  have hE := solveSub _ _ _ hall
  rw [hU] at hR
  rw [hR] at hE
  exact hE

theorem shadow_cover_bound [Fintype V] (A S T : Finset V) (p q : ℕ) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      shadowCost (Fintype.card V) A.card
        (A ∩ S).card ((univ \ A) ∩ S).card
        (A ∩ T).card ((univ \ A) ∩ T).card
        (A ∩ (S ∩ T)).card ((univ \ A) ∩ (S ∩ T)).card := by
  apply coverNumber_le_of_budget
  refine ⟨(shadowCore A S T).image (lift (C := Fin p ⊕ Fin q)),shadow_isCover A S T p q,?_⟩
  rw [card_image_of_injective _ lift_injective,shadowCore_card]

#print axioms pairOf_injOn
#print axioms lifted_core_cover
#print axioms shadow_isCover
#print axioms shadowCore_card
#print axioms shadow_cover_bound
#check shadow_cover_bound
end TuzaShadowCovers

/-! Explicit mass assignments for the four continuous cover formulas. -/
namespace TuzaCutFormulas

structure Geometry (k s t u : ℝ) : Prop where
  k_nonneg : 0 ≤ k
  u_nonneg : 0 ≤ u
  u_le_s : u ≤ s
  s_le_t : s ≤ t
  t_le_k : t ≤ k
  union_le : s+t-u ≤ k
  t_large : k/2 ≤ t
  exclusive_small : s-u ≤ k/2

def Feasible (k s t u a b c d : ℝ) : Prop :=
  (0 ≤ a ∧ a ≤ s-u) ∧ (0 ≤ b ∧ b ≤ t-u) ∧
  (0 ≤ c ∧ c ≤ u) ∧ (0 ≤ d ∧ d ≤ k-s-t+u) ∧ a+b+c+d = k/2

set_option maxHeartbeats 1200000 in
theorem order_one (k s t u : ℝ) (h : Geometry k s t u) :
    ∃ a b c d : ℝ, Feasible k s t u a b c d ∧
      s-a-c = max 0 (s-k/2) ∧
      t-b-c = max 0 (t-min u (k/2)-max 0 (k/2-s)) := by
  obtain ⟨hk,hu,hus,hst,htk,hunion,htlarge,ha⟩ := h
  refine ⟨min s (k/2)-min u (k/2),max 0 (k/2-s),min u (k/2),0,?_⟩
  unfold Feasible
  simp only [min_def,max_def]
  split_ifs <;> (repeat' constructor) <;> linarith

theorem order_two (k s t u : ℝ) (h : Geometry k s t u) :
    ∃ a b c d : ℝ, Feasible k s t u a b c d ∧
      s-a-c = s-min u (k/2) ∧ t-b-c = t-k/2 := by
  obtain ⟨hk,hu,hus,hst,htk,hunion,htlarge,ha⟩ := h
  refine ⟨0,k/2-min u (k/2),min u (k/2),0,?_⟩
  unfold Feasible
  simp only [min_def]
  split_ifs <;> (repeat' constructor) <;> linarith

theorem order_three (k s t u : ℝ) (h : Geometry k s t u) :
    ∃ a b c d : ℝ, Feasible k s t u a b c d ∧
      s-a-c = max 0 (s-k/2) ∧ b+c = max (t-k/2) (u-max 0 (s-k/2)) := by
  obtain ⟨hk,hu,hus,hst,htk,hunion,htlarge,ha⟩ := h
  refine ⟨s-u,max 0 (k/2-s)-min (k-s-t+u) (max 0 (k/2-s)),
    u-max 0 (s-k/2),min (k-s-t+u) (max 0 (k/2-s)),?_⟩
  unfold Feasible
  simp only [min_def,max_def]
  split_ifs <;> (repeat' constructor) <;> linarith

theorem order_four (k s t u : ℝ) (h : Geometry k s t u) :
    ∃ a b c d : ℝ, Feasible k s t u a b c d ∧
      s-a-c = max 0 (u-t+k/2) ∧ b+c = t-k/2 := by
  obtain ⟨hk,hu,hus,hst,htk,hunion,htlarge,ha⟩ := h
  refine ⟨s-u,t-k/2-min u (t-k/2),min u (t-k/2),k-s-t+u,?_⟩
  unfold Feasible
  simp only [min_def,max_def]
  split_ifs <;> (repeat' constructor) <;> linarith

open Finset TuzaFractionalOrders TuzaSeparableCover TuzaBalancedRounding
  TuzaCoverCompression TuzaIndependentAllocation
variable {V : Type*} [DecidableEq V] [Fintype V]

theorem outside_card (S T : Finset V) :
    ((outside S T).card : ℝ) = (Fintype.card V : ℝ)-S.card-T.card+(S ∩ T).card := by
  have h1 : ((outside S T).card : ℝ)+(S ∪ T).card = (Fintype.card V : ℝ) := by
    have hh := card_sdiff_add_card_eq_card (subset_univ (S ∪ T))
    simp only [card_univ] at hh
    exact_mod_cast hh
  have h2 : ((S ∪ T).card : ℝ)+(S ∩ T).card = (S.card : ℝ)+T.card := by
    exact_mod_cast card_union_add_card_inter S T
  linarith

theorem geometry_of_sets (S T : Finset V) (hst : S.card ≤ T.card)
    (ht : (Fintype.card V : ℝ)/2 ≤ (T.card : ℝ)) :
    Geometry (Fintype.card V) S.card T.card (S ∩ T).card := by
  have hu0 : (0 : ℝ) ≤ (S ∩ T).card := by positivity
  have hus : ((S ∩ T).card : ℝ) ≤ S.card := by exact_mod_cast card_le_card inter_subset_left
  have hst' : (S.card : ℝ) ≤ T.card := by exact_mod_cast hst
  have htK : (T.card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ T
  have hUnion : (S.card : ℝ)+(T.card : ℝ)-(S ∩ T).card ≤ Fintype.card V := by
    have h0 : (0 : ℝ) ≤ (outside S T).card := by positivity
    rw [outside_card] at h0
    linarith
  exact ⟨by positivity,hu0,hus,hst',htK,hUnion,ht,by linarith⟩

theorem feasible_cover (S T : Finset V) (p q : ℕ) (a b c d : ℝ) (bs bt : Bool)
    (h : Feasible (Fintype.card V) S.card T.card (S ∩ T).card a b c d) :
    (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) ≤
      (coreBudget (Fintype.card V) : ℝ) +
        p*(if bs then a+c else (S.card : ℝ)-a-c) +
        q*(if bt then b+c else (T.card : ℝ)-b-c) := by
  obtain ⟨ha,hb,hc,hd,hm⟩ := h
  apply four_region_cover S T p q a b c d bs bt
  · rw [(region_sizes S T).1]; exact ha
  · rw [(region_sizes S T).2]; exact hb
  · exact hc
  · rw [outside_card]; exact hd
  · exact hm

noncomputable def costOne (k s t u p q : ℝ) : ℝ :=
  p*max 0 (s-k/2)+q*max 0 (t-min u (k/2)-max 0 (k/2-s))
noncomputable def costTwo (k s t u p q : ℝ) : ℝ :=
  q*(t-k/2)+p*(s-min u (k/2))
noncomputable def costThree (k s t u p q : ℝ) : ℝ :=
  p*max 0 (s-k/2)+q*max (t-k/2) (u-max 0 (s-k/2))
noncomputable def costFour (k s t u p q : ℝ) : ℝ :=
  q*(t-k/2)+p*max 0 (u-t+k/2)

theorem four_balanced_bounds (S T : Finset V) (p q : ℕ) (hst : S.card ≤ T.card)
    (ht : (Fintype.card V : ℝ)/2 ≤ (T.card : ℝ)) :
    let k : ℝ := Fintype.card V
    let s : ℝ := S.card
    let t : ℝ := T.card
    let u : ℝ := (S ∩ T).card
    let c : ℝ := coreBudget (Fintype.card V)
    let tau : ℝ := coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q))
    tau ≤ c+costOne k s t u p q ∧ tau ≤ c+costTwo k s t u p q ∧
      tau ≤ c+costThree k s t u p q ∧ tau ≤ c+costFour k s t u p q := by
  dsimp
  have hgeom := geometry_of_sets S T hst ht
  refine ⟨?_,?_,?_,?_⟩
  · obtain ⟨a,b,c,d,hf,hS,hT⟩ := order_one _ _ _ _ hgeom
    have hh := feasible_cover S T p q a b c d false false hf
    simpa [hS,hT,costOne,add_assoc] using hh
  · obtain ⟨a,b,c,d,hf,hS,hT⟩ := order_two _ _ _ _ hgeom
    have hh := feasible_cover S T p q a b c d false false hf
    simpa [hS,hT,costTwo,add_assoc,add_comm,add_left_comm] using hh
  · obtain ⟨a,b,c,d,hf,hS,hT⟩ := order_three _ _ _ _ hgeom
    have hh := feasible_cover S T p q a b c d false true hf
    simpa [hS,hT,costThree,add_assoc] using hh
  · obtain ⟨a,b,c,d,hf,hS,hT⟩ := order_four _ _ _ _ hgeom
    have hh := feasible_cover S T p q a b c d false true hf
    simpa [hS,hT,costFour,add_assoc,add_comm,add_left_comm] using hh

#print axioms order_one
#print axioms order_two
#print axioms order_three
#print axioms order_four
#print axioms geometry_of_sets
#print axioms feasible_cover
#print axioms four_balanced_bounds
#check four_balanced_bounds
end TuzaCutFormulas

/-! Transport of graph optima and compression of both outer types. -/
namespace TuzaGraphTransfer
open Finset TuzaCompression TuzaGraphCompression TuzaCoverCompression
  TuzaIndependentAllocation TuzaGraphBounds
variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]

theorem map_cover (H : SimpleGraph V) (G : SimpleGraph W) (f : V → W)
    (hf : Function.Injective f) (hadj : ∀ a b, H.Adj a b → G.Adj (f a) (f b))
    (htri : ∀ t, G.IsNClique 3 t → ∃ u, H.IsNClique 3 u ∧ u.image f = t)
    (F : Finset (Finset V)) (hF : IsCover H F) :
    IsCover G (F.image (fun e => e.image f)) := by
  refine ⟨?_,?_⟩
  · intro e he
    obtain ⟨d,hd,rfl⟩ := mem_image.mp he
    exact image_clique f hf hadj (hF.1 d hd)
  · intro t ht
    obtain ⟨u,hu,rfl⟩ := htri t ht
    obtain ⟨e,he,heu⟩ := hF.2 u hu
    exact ⟨e.image f,mem_image.mpr ⟨e,he,rfl⟩,image_subset_image heu⟩

theorem coverNumber_map_le (H : SimpleGraph V) (G : SimpleGraph W) (f : V → W)
    (hf : Function.Injective f) (hadj : ∀ a b, H.Adj a b → G.Adj (f a) (f b))
    (htri : ∀ t, G.IsNClique 3 t → ∃ u, H.IsNClique 3 u ∧ u.image f = t) :
    coverNumber G ≤ coverNumber H := by
  obtain ⟨F,hF,hFc⟩ := coverNumber_budget H
  apply coverNumber_le_of_budget
  refine ⟨F.image (fun e => e.image f),map_cover H G f hf hadj htri F hF,?_⟩
  rwa [card_image_of_injective _ (Finset.image_injective hf)]

theorem tuza_transfer (H : SimpleGraph V) (G : SimpleGraph W) (f : V → W)
    (hf : Function.Injective f) (hadj : ∀ a b, H.Adj a b → G.Adj (f a) (f b))
    (htri : ∀ t, G.IsNClique 3 t → ∃ u, H.IsNClique 3 u ∧ u.image f = t)
    (hTuza : coverNumber H ≤ 2*packingNumber H) : coverNumber G ≤ 2*packingNumber G := by
  exact (coverNumber_map_le H G f hf hadj htri).trans
    (hTuza.trans (Nat.mul_le_mul_left 2 (packingNumber_map_le H G f hf hadj)))

theorem iso_triangles (H : SimpleGraph V) (G : SimpleGraph W) (e : V ≃ W)
    (hadj : ∀ a b, H.Adj a b ↔ G.Adj (e a) (e b)) :
    ∀ t, G.IsNClique 3 t → ∃ u, H.IsNClique 3 u ∧ u.image e = t := by
  intro t ht
  refine ⟨t.image e.symm,?_,?_⟩
  · apply image_clique e.symm e.symm.injective ?_ ht
    intro a b hab
    exact (hadj _ _).mpr (by simpa using hab)
  · ext w
    simp only [mem_image]
    constructor
    · rintro ⟨v,⟨x,hx,rfl⟩,rfl⟩
      simpa using hx
    · intro hw
      exact ⟨e.symm w,⟨w,hw,rfl⟩,by simp⟩

theorem iso_parameters (H : SimpleGraph V) (G : SimpleGraph W) (e : V ≃ W)
    (hadj : ∀ a b, H.Adj a b ↔ G.Adj (e a) (e b)) :
    packingNumber H = packingNumber G ∧ coverNumber H = coverNumber G := by
  have hi : ∀ a b, G.Adj a b ↔ H.Adj (e.symm a) (e.symm b) := by
    intro a b
    simpa using (hadj (e.symm a) (e.symm b)).symm
  constructor
  · exact Nat.le_antisymm
      (packingNumber_map_le H G e e.injective (fun a b h => (hadj a b).mp h))
      (packingNumber_map_le G H e.symm e.symm.injective (fun a b h => (hi a b).mp h))
  · exact Nat.le_antisymm
      (coverNumber_map_le G H e.symm e.symm.injective (fun a b h => (hi a b).mp h)
        (iso_triangles G H e.symm hi))
      (coverNumber_map_le H G e e.injective (fun a b h => (hadj a b).mp h)
        (iso_triangles H G e hadj))

theorem nested_adjacency (S T : Finset V) (p q : ℕ)
    (a b : (V ⊕ Fin p) ⊕ Fin q) :
    (attached (attached (⊤ : SimpleGraph V) S (Fin p)) (T.image Sum.inl) (Fin q)).Adj a b ↔
      (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)).Adj
        (Equiv.sumAssoc V (Fin p) (Fin q) a) (Equiv.sumAssoc V (Fin p) (Fin q) b) := by
  cases a with
  | inl a =>
    cases b with
    | inl b => cases a <;> cases b <;> simp [attached,twoAttached,neighborhood,Equiv.sumAssoc]
    | inr b => cases a <;> simp [attached,twoAttached,neighborhood,Equiv.sumAssoc]
  | inr a =>
    cases b with
    | inl b => cases b <;> simp [attached,twoAttached,neighborhood,Equiv.sumAssoc]
    | inr b => simp [attached,twoAttached,Equiv.sumAssoc]

theorem nested_parameters (S T : Finset V) (p q : ℕ) :
    packingNumber (attached (attached (⊤ : SimpleGraph V) S (Fin p)) (T.image Sum.inl) (Fin q)) =
      packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ∧
    coverNumber (attached (attached (⊤ : SimpleGraph V) S (Fin p)) (T.image Sum.inl) (Fin q)) =
      coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) :=
  iso_parameters _ _ (Equiv.sumAssoc V (Fin p) (Fin q)) (nested_adjacency S T p q)

theorem compress_second_type (S T : Finset V) (ht : 2 ≤ T.card) (p q : ℕ) :
    packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) =
      packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin (min q (colorCount T.card)))) ∧
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) =
      coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin (min q (colorCount T.card)))) := by
  have he : (T.image (Sum.inl : V → V ⊕ Fin p)).card = T.card :=
    card_image_of_injective _ Sum.inl_injective
  have h := both_parameters_attached_min (attached (⊤ : SimpleGraph V) S (Fin p))
    (T.image Sum.inl) (by rw [he]; exact ht) q
  rw [he] at h
  have h1 := nested_parameters S T p q
  have h2 := nested_parameters S T p (min q (colorCount T.card))
  exact ⟨h1.1.symm.trans (h.1.trans h2.1),h1.2.symm.trans (h.2.trans h2.2)⟩

theorem swap_types (S T : Finset V) (p q : ℕ) :
    packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) =
      packingNumber (twoAttached (⊤ : SimpleGraph V) T S (Fin q) (Fin p)) ∧
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) =
      coverNumber (twoAttached (⊤ : SimpleGraph V) T S (Fin q) (Fin p)) := by
  let e := Equiv.sumCongr (Equiv.refl V) (Equiv.sumComm (Fin p) (Fin q))
  apply iso_parameters _ _ e
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b => cases b <;> rfl
  | inr a =>
    cases b with
    | inl b => cases a <;> rfl
    | inr b => rfl

theorem compress_both_types (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card) (p q : ℕ) :
    packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) =
      packingNumber (twoAttached (⊤ : SimpleGraph V) S T
        (Fin (min p (colorCount S.card))) (Fin (min q (colorCount T.card)))) ∧
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) =
      coverNumber (twoAttached (⊤ : SimpleGraph V) S T
        (Fin (min p (colorCount S.card))) (Fin (min q (colorCount T.card)))) := by
  have h0 := compress_second_type S T ht p q
  have h1 := swap_types S T p (min q (colorCount T.card))
  have h2 := compress_second_type T S hs (min q (colorCount T.card)) p
  have h3 := swap_types T S (min q (colorCount T.card)) (min p (colorCount S.card))
  exact ⟨h0.1.trans (h1.1.trans (h2.1.trans h3.1)),h0.2.trans (h1.2.trans (h2.2.trans h3.2))⟩

#print axioms map_cover
#print axioms tuza_transfer
#print axioms iso_parameters
#print axioms nested_parameters
#print axioms compress_second_type
#print axioms swap_types
#print axioms compress_both_types
#check compress_both_types
end TuzaGraphTransfer

/-! Graph witnesses for the real packing inequalities. -/
namespace TuzaPackingInterfaces
open Finset TuzaCompression TuzaGraphCompression TuzaMatchingClasses
  TuzaIndependentAllocation TuzaCoupledAllocation TuzaCoreCompletion TuzaRealBounds
variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def independentRate (s t u p q : ℕ) : ℝ :=
  (p : ℝ)/s * s.choose 2 + (q : ℝ)/t * t.choose 2 -
    ((p : ℝ)/s)*((q : ℝ)/t)*u.choose 2

noncomputable def coupledRate (s t u p q : ℕ) : ℝ :=
  ((p : ℝ)*s.choose 2+(q : ℝ)*t.choose 2-
    max 0 ((p : ℝ)+q-t)*u.choose 2)/t

theorem choose_inter_bounds (S T : Finset V) :
    (S ∩ T).card.choose 2 ≤ S.card.choose 2 ∧
    (S ∩ T).card.choose 2 ≤ T.card.choose 2 := by
  constructor
  · have h : (S ∩ T).powersetCard 2 ⊆ S.powersetCard 2 := by
      intro e he
      obtain ⟨he,hc⟩ := mem_powersetCard.mp he
      exact mem_powersetCard.mpr ⟨he.trans inter_subset_left,hc⟩
    simpa only [card_powersetCard] using card_le_card h
  · have h : (S ∩ T).powersetCard 2 ⊆ T.powersetCard 2 := by
      intro e he
      obtain ⟨he,hc⟩ := mem_powersetCard.mp he
      exact mem_powersetCard.mpr ⟨he.trans inter_subset_right,hc⟩
    simpa only [card_powersetCard] using card_le_card h

theorem cast_sub_max (a b : ℕ) : ((a-b : ℕ) : ℝ) = max 0 ((a : ℝ)-b) := by
  by_cases h : b ≤ a
  · rw [Nat.cast_sub h, max_eq_right]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · have hle : a ≤ b := by omega
    rw [Nat.sub_eq_zero_of_le hle, Nat.cast_zero, max_eq_left]
    exact sub_nonpos.mpr (by exact_mod_cast hle)

theorem independent_witness (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card)
    (p q : ℕ) (hp : p ≤ colorCount S.card) (hq : q ≤ colorCount T.card) :
    ∃ P : Finset (Finset (V ⊕ (Fin p ⊕ Fin q))),
      IsPacking (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) P ∧
      independentRate S.card T.card (S ∩ T).card p q ≤ (P.card : ℝ) ∧
      ∀ t ∈ P, t.toRight.Nonempty := by
  obtain ⟨P,hP,hb,hout⟩ := independent_allocation (⊤ : SimpleGraph V) S T hs ht
    (by intro a ha b hb hab; exact hab) (by intro a ha b hb hab; exact hab) p q
  rw [min_eq_left hp,min_eq_left hq] at hb
  have ha := palette_bounds S.card hs
  have hc := palette_bounds T.card ht
  have hu := choose_inter_bounds S T
  refine ⟨P,hP,?_,hout⟩
  unfold independentRate
  apply independent_relaxation (S.card : ℝ) (T.card : ℝ)
    (colorCount S.card) (colorCount T.card) p q (S.card.choose 2) (T.card.choose 2)
    ((S ∩ T).card.choose 2) P.card
  · exact_mod_cast ha
  · exact_mod_cast hc
  · exact ⟨by positivity,by exact_mod_cast hp⟩
  · exact ⟨by positivity,by exact_mod_cast hq⟩
  · exact ⟨by positivity,by exact_mod_cast hu.1,by exact_mod_cast hu.2⟩
  · exact_mod_cast hb

theorem coupled_witness (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card)
    (hst : S.card ≤ T.card) (p q : ℕ)
    (hp : p ≤ colorCount S.card) (hq : q ≤ colorCount T.card) :
    ∃ P : Finset (Finset (V ⊕ (Fin p ⊕ Fin q))),
      IsPacking (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) P ∧
      coupledRate S.card T.card (S ∩ T).card p q ≤ (P.card : ℝ) ∧
      ∀ t ∈ P, t.toRight.Nonempty := by
  obtain ⟨P,hP,hb,hout⟩ := coupled_allocation (⊤ : SimpleGraph V) S T hs ht
    (by intro a ha b hb hab; exact hab) (by intro a ha b hb hab; exact hab) p q
  have hpT := hp.trans (palette_mono S.card T.card hst)
  rw [max_eq_right hst,min_eq_left hpT,min_eq_left hq] at hb
  have hc := palette_bounds T.card ht
  have hu := choose_inter_bounds S T
  have hbR : (p : ℝ)*S.card.choose 2+(q : ℝ)*T.card.choose 2 ≤
      (colorCount T.card : ℝ)*P.card+
      ((p+q-colorCount T.card : ℕ) : ℝ)*(S ∩ T).card.choose 2 := by exact_mod_cast hb
  rw [cast_sub_max, Nat.cast_add] at hbR
  refine ⟨P,hP,?_,hout⟩
  unfold coupledRate
  apply coupled_relaxation (colorCount T.card) (T.card : ℝ) p q (S.card.choose 2)
    (T.card.choose 2) ((S ∩ T).card.choose 2) P.card
  · exact_mod_cast hc
  · positivity
  · positivity
  · exact ⟨by positivity,by exact_mod_cast hu.1,by exact_mod_cast hu.2⟩
  · exact hbR

/-- A single packing realizes the larger of the two real lower bounds. -/
theorem outside_witness (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card)
    (hst : S.card ≤ T.card) (p q : ℕ)
    (hp : p ≤ colorCount S.card) (hq : q ≤ colorCount T.card) :
    ∃ P : Finset (Finset (V ⊕ (Fin p ⊕ Fin q))),
      IsPacking (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) P ∧
      max (independentRate S.card T.card (S ∩ T).card p q)
        (coupledRate S.card T.card (S ∩ T).card p q) ≤ (P.card : ℝ) ∧
      ∀ t ∈ P, t.toRight.Nonempty := by
  by_cases h : independentRate S.card T.card (S ∩ T).card p q ≤
      coupledRate S.card T.card (S ∩ T).card p q
  · rw [max_eq_right h]
    exact coupled_witness S T hs ht hst p q hp hq
  · rw [max_eq_left (le_of_not_ge h)]
    exact independent_witness S T hs ht p q hp hq

/-- Both inequalities use the same centered packing and its verified completion. -/
theorem outside_and_completion (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card)
    (hst : S.card ≤ T.card) (p q : ℕ)
    (hp : p ≤ colorCount S.card) (hq : q ≤ colorCount T.card) :
    let L := max (independentRate S.card T.card (S ∩ T).card p q)
      (coupledRate S.card T.card (S ∩ T).card p q)
    let nu := packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q))
    L ≤ (nu : ℝ) ∧ 2*L+(Fintype.card V).choose 2 ≤
      3*(nu : ℝ)+((Fintype.card V)^2 / 4 : ℕ) := by
  obtain ⟨P,hP,hL,hout⟩ := outside_witness S T hs ht hst p q hp hq
  have hc := core_completion_bound (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q))
    (by intro a b h; exact h) (by intro a b h; exact h) P hP hout
  have h1 : (P.card : ℝ) ≤ packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by exact_mod_cast hc.1
  have h2 : 2*(P.card : ℝ)+(Fintype.card V).choose 2 ≤
      3*(packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ)+
        ((Fintype.card V)^2 / 4 : ℕ) := by exact_mod_cast hc.2
  exact ⟨hL.trans h1,by linarith only [hL,h2]⟩

#print axioms choose_inter_bounds
#print axioms cast_sub_max
#print axioms independent_witness
#print axioms coupled_witness
#print axioms outside_witness
#print axioms outside_and_completion
#check outside_and_completion
end TuzaPackingInterfaces

/-! Realization of integer region cuts used by both certificates. -/
namespace TuzaRegionCuts
open Finset TuzaCompression TuzaFractionalOrders TuzaShadowCovers TuzaCoverCompression
  TuzaIndependentAllocation TuzaCutCovers TuzaBalancedRounding TuzaCommonRounding
variable {V : Type*} [DecidableEq V] [Fintype V]

theorem disjoint_regions (S T : Finset V) :
    Disjoint (S \ T) (T \ S) ∧ Disjoint (S \ T) (S ∩ T) ∧
    Disjoint (S \ T) (outside S T) ∧ Disjoint (T \ S) (S ∩ T) ∧
    Disjoint (T \ S) (outside S T) ∧ Disjoint (S ∩ T) (outside S T) := by
  simp only [disjoint_left,mem_sdiff,mem_inter,outside,mem_union,mem_univ]
  tauto

set_option maxHeartbeats 800000 in
/-- Every feasible set of four integer masses is realized by an actual cut. -/
theorem realize_regions (S T : Finset V) (a b c d : ℕ)
    (ha : a ≤ (S \ T).card) (hb : b ≤ (T \ S).card)
    (hc : c ≤ (S ∩ T).card) (hd : d ≤ (outside S T).card) :
    ∃ L : Finset V, L.card = a+b+c+d ∧
      (L ∩ S).card = a+c ∧ (L ∩ T).card = b+c ∧ (L ∩ (S ∩ T)).card = c ∧
      ((univ \ L) ∩ S).card = S.card-(a+c) ∧
      ((univ \ L) ∩ T).card = T.card-(b+c) ∧
      ((univ \ L) ∩ (S ∩ T)).card = (S ∩ T).card-c := by
  obtain ⟨A,hA,hAc⟩ := exists_subset_card_eq ha
  obtain ⟨B,hB,hBc⟩ := exists_subset_card_eq hb
  obtain ⟨U,hU,hUc⟩ := exists_subset_card_eq hc
  obtain ⟨O,hO,hOc⟩ := exists_subset_card_eq hd
  obtain ⟨hAB,hAU,hAO,hBU,hBO,hUO⟩ := disjoint_regions S T
  have dAB := hAB.mono hA hB
  have dAU := hAU.mono hA hU
  have dAO := hAO.mono hA hO
  have dBU := hBU.mono hB hU
  have dBO := hBO.mono hB hO
  have dUO := hUO.mono hU hO
  let L := A ∪ B ∪ U ∪ O
  have hLc : L.card = a+b+c+d := by
    dsimp only [L]
    rw [card_union_of_disjoint (disjoint_union_left.mpr
      ⟨disjoint_union_left.mpr ⟨dAO,dBO⟩,dUO⟩),
      card_union_of_disjoint (disjoint_union_left.mpr ⟨dAU,dBU⟩),
      card_union_of_disjoint dAB,hAc,hBc,hUc,hOc]
  have hAS (v : V) : v ∈ A → v ∈ S ∧ v ∉ T := fun hv => mem_sdiff.mp (hA hv)
  have hBS (v : V) : v ∈ B → v ∈ T ∧ v ∉ S := fun hv => mem_sdiff.mp (hB hv)
  have hUS (v : V) : v ∈ U → v ∈ S ∧ v ∈ T := fun hv => mem_inter.mp (hU hv)
  have hOS (v : V) : v ∈ O → v ∉ S ∧ v ∉ T := by
    intro hv
    have hx := (mem_sdiff.mp (hO hv)).2
    simpa only [mem_union,not_or] using hx
  have hLS : L ∩ S = A ∪ U := by
    ext v
    simp only [L,mem_inter,mem_union]
    have := hAS v; have := hBS v; have := hUS v; have := hOS v
    tauto
  have hLT : L ∩ T = B ∪ U := by
    ext v
    simp only [L,mem_inter,mem_union]
    have := hAS v; have := hBS v; have := hUS v; have := hOS v
    tauto
  have hLU : L ∩ (S ∩ T) = U := by
    ext v
    simp only [L,mem_inter,mem_union]
    have := hAS v; have := hBS v; have := hUS v; have := hOS v
    tauto
  have hLSc : (L ∩ S).card = a+c := by rw [hLS,card_union_of_disjoint dAU,hAc,hUc]
  have hLTc : (L ∩ T).card = b+c := by rw [hLT,card_union_of_disjoint dBU,hBc,hUc]
  have hLUc : (L ∩ (S ∩ T)).card = c := by rw [hLU,hUc]
  have hcomp (R : Finset V) : ((univ \ L) ∩ R).card = R.card-(L ∩ R).card := by
    have he : (univ \ L) ∩ R = R \ L := by ext v; simp; tauto
    rw [he,card_sdiff,inter_comm]
  exact ⟨L,hLc,hLSc,hLTc,hLUc,by rw [hcomp S,hLSc],
    by rw [hcomp T,hLTc],by rw [hcomp (S ∩ T),hLUc]⟩

theorem integer_region_shadow (S T : Finset V) (p q a b c d : ℕ)
    (ha : a ≤ (S \ T).card) (hb : b ≤ (T \ S).card)
    (hc : c ≤ (S ∩ T).card) (hd : d ≤ (outside S T).card) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      shadowCost (Fintype.card V) (a+b+c+d) (a+c) (S.card-(a+c))
        (b+c) (T.card-(b+c)) c ((S ∩ T).card-c) := by
  obtain ⟨L,hLc,hLS,hLT,hLU,hRS,hRT,hRU⟩ := realize_regions S T a b c d ha hb hc hd
  have hh := shadow_cover_bound L S T p q
  simpa only [hLc,hLS,hLT,hLU,hRS,hRT,hRU] using hh


/-- The counting identity before any natural-number subtraction. -/
theorem shadow_balance (A S T : Finset V) :
    (shadowCore A S T).card + A.card*(Fintype.card V-A.card) +
      (A ∩ (S ∩ T)).card*((univ \ A) ∩ (S ∩ T)).card =
    (Fintype.card V).choose 2 + (A ∩ S).card*((univ \ A) ∩ S).card +
      (A ∩ T).card*((univ \ A) ∩ T).card := by
  let R : Finset V := univ \ A
  have hd : Disjoint A R := by apply disjoint_left.mpr; intro v hv hr; exact (mem_sdiff.mp hr).2 hv
  have hinj := pairOf_injOn A R hd
  have himage : ((retained A S T).image pairOf).card = (retained A S T).card :=
    card_image_of_injOn (fun x hx y hy h => hinj (retained_subset A S T hx) (retained_subset A S T hy) h)
  have hsub : crossProduct A R S ∪ crossProduct A R T ⊆ A.product R := by
    intro v hv
    rcases mem_union.mp hv with hv | hv <;>
      exact mem_product.mpr ⟨(mem_inter.mp (mem_product.mp hv).1).1,(mem_inter.mp (mem_product.mp hv).2).1⟩
  have hinter : crossProduct A R S ∩ crossProduct A R T = crossProduct A R (S ∩ T) := by
    ext v
    simp [crossProduct,and_assoc,and_left_comm,and_comm]
  have hcount := card_sdiff_add_card_eq_card hsub
  have hunion := card_union_add_card_inter (crossProduct A R S) (crossProduct A R T)
  rw [hinter] at hunion
  simp only [crossProduct,product_eq_sprod,card_product] at hunion
  change (retained A S T).card + _ = _ at hcount
  rw [product_eq_sprod,card_product,show R.card = Fintype.card V-A.card by simp [R,card_sdiff_of_subset (subset_univ A)]] at hcount
  have hall := card_sdiff_add_card_eq_card (retained_edges A S T)
  change (shadowCore A S T).card + _ = _ at hall
  rw [himage,card_powersetCard,card_univ] at hall
  change (crossProduct A R S ∪ crossProduct A R T).card +
    (A ∩ (S ∩ T)).card*(R ∩ (S ∩ T)).card =
    (A ∩ S).card*(R ∩ S).card+(A ∩ T).card*(R ∩ T).card at hunion
  dsimp only [R] at hcount hunion
  omega

theorem integer_region_cut (S T : Finset V) (p q a b c d : ℕ)
    (ha : a ≤ (S \ T).card) (hb : b ≤ (T \ S).card)
    (hc : c ≤ (S ∩ T).card) (hd : d ≤ (outside S T).card) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      (a+b+c+d).choose 2 + (Fintype.card V-(a+b+c+d)).choose 2 +
        p*min (a+c) (S.card-(a+c)) + q*min (b+c) (T.card-(b+c)) := by
  obtain ⟨L,hLc,hLS,hLT,hLU,hRS,hRT,hRU⟩ := realize_regions S T a b c d ha hb hc hd
  have hh := two_type_cover_bound L S T p q
  rw [inter_comm S L,inter_comm T L] at hh
  simp only [card_sdiff,hLc,hLS,hLT] at hh
  exact hh

theorem large_shadow (S T : Finset V) (p q : ℕ) :
    (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) ≤
      (Fintype.card V).choose 2 - (T.card : ℝ)*((Fintype.card V : ℝ)-T.card)+
        (S.card : ℝ)*(S ∩ T).card-((S ∩ T).card : ℝ)^2 := by
  let A : Finset V := univ \ T
  have hAc : A.card = Fintype.card V-T.card := by simp [A,card_sdiff_of_subset (subset_univ T)]
  have hAS : A ∩ S = S \ T := by ext v; simp [A] <;> tauto
  have hAT : A ∩ T = ∅ := by ext v; simp [A] <;> tauto
  have hAU : A ∩ (S ∩ T) = ∅ := by ext v; simp [A] <;> tauto
  have hRS : (univ \ A) ∩ S = S ∩ T := by ext v; simp [A] <;> tauto
  have hh := shadow_balance A S T
  simp only [hAc,hAS,hAT,hAU,hRS,card_empty,zero_mul,add_zero] at hh
  have htK := card_le_univ T
  have huS : (S ∩ T).card ≤ S.card := card_le_card inter_subset_left
  rw [Nat.sub_sub_self htK,card_sdiff,inter_comm T S] at hh
  have hhR : ((shadowCore A S T).card : ℝ)+
      ((Fintype.card V-T.card : ℕ) : ℝ)*T.card =
      (Fintype.card V).choose 2+((S.card-(S ∩ T).card : ℕ) : ℝ)*(S ∩ T).card := by exact_mod_cast hh
  rw [Nat.cast_sub htK,Nat.cast_sub huS] at hhR
  have hc : coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      (shadowCore A S T).card := by
    apply coverNumber_le_of_budget
    refine ⟨(shadowCore A S T).image (lift (C := Fin p ⊕ Fin q)),shadow_isCover A S T p q,?_⟩
    rw [card_image_of_injective _ lift_injective]
  have hcR : (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) ≤
      (shadowCore A S T).card := by exact_mod_cast hc
  nlinarith only [hhR,hcR]


theorem core_floor_le (k : ℕ) (hk : 2 ≤ k) : k^2/4 ≤ k.choose 2 := by
  have h0 := choose_two_real k
  have hd : (((k^2/4 : ℕ) : ℝ))*4 ≤ (k : ℝ)^2 := by
    exact_mod_cast Nat.div_mul_le_self (k^2) 4
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hprod : 0 ≤ (k : ℝ)*((k : ℝ)-2) := mul_nonneg (by positivity) (by linarith)
  have hle : ((k^2/4 : ℕ) : ℝ) ≤ (k.choose 2 : ℝ) := by nlinarith only [h0,hd,hprod]
  exact_mod_cast hle

theorem small_shadow (S T : Finset V) (p q : ℕ) (hk : 2 ≤ Fintype.card V)
    (hst : S.card ≤ T.card) (ht : T.card ≤ Fintype.card V/2) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      coreBudget (Fintype.card V)+(S \ T).card*(S ∩ T).card := by
  let k := Fintype.card V
  let a := (S \ T).card
  let z := k/2-a
  have h1 := card_sdiff_add_card_inter S T
  have h2 := card_union_add_card_inter S T
  have h3 := card_sdiff_add_card_eq_card (subset_univ (S ∪ T))
  change (outside S T).card+(S ∪ T).card = (univ : Finset V).card at h3
  simp only [card_univ] at h3
  have ha : a ≤ k/2 := by dsimp [a,k]; omega
  have hz : z ≤ (outside S T).card := by dsimp [z,k,a]; omega
  obtain ⟨L,hLc,hLS,hLT,hLU,hRS,hRT,hRU⟩ := realize_regions S T a 0 0 z
    (by rfl) (Nat.zero_le _) (Nat.zero_le _) hz
  simp only [Nat.add_zero,zero_add,Nat.sub_zero] at hLc hLS hLT hLU hRS hRT hRU
  have hLhalf : L.card = k/2 := by dsimp [z] at hLc; omega
  have hSu : S.card-a = (S ∩ T).card := by dsimp [a]; omega
  have hbal := shadow_balance L S T
  rw [hLhalf,hLS,hLT,hLU,hRS,hRT,hRU,hSu] at hbal
  simp only [zero_mul,Nat.add_zero] at hbal
  have hprod : (k/2)*(k-k/2) = k^2/4 := by
    rw [show k-k/2 = (k+1)/2 by omega,half_product]
  change (shadowCore L S T).card+(k/2)*(k-k/2) = k.choose 2+a*(S ∩ T).card at hbal
  rw [hprod] at hbal
  have hle := core_floor_le k hk
  have he : coreBudget k+k^2/4 = k.choose 2 := Nat.sub_add_cancel hle
  have hcost : (shadowCore L S T).card = coreBudget k+a*(S ∩ T).card := by omega
  apply coverNumber_le_of_budget
  refine ⟨(shadowCore L S T).image (lift (C := Fin p ⊕ Fin q)),shadow_isCover L S T p q,?_⟩
  rw [card_image_of_injective _ lift_injective,hcost]

#print axioms core_floor_le
#print axioms small_shadow
#print axioms shadow_balance
#print axioms integer_region_cut
#print axioms large_shadow
#print axioms disjoint_regions
#print axioms realize_regions
#print axioms integer_region_shadow
#check integer_region_shadow
end TuzaRegionCuts

/-! Scalar analytic reductions, with explicit polynomial certificates. -/
namespace TuzaAnalytic
open TuzaSeparableCover

noncomputable def P (k m : ℝ) : ℝ :=
  4*k^3-24*k^2+20*k-9*m*k^2+12*m*k-12*m^2-24*m-3*m^3
noncomputable def Q (k m : ℝ) : ℝ := k^3-6*k^2+5*k-3*m^3-6*m^2-6*m
noncomputable def F (k d m : ℝ) : ℝ :=
  k*(k-1)*(k-2)/3+m*d*(d-1)-(k+m)*((k-1)^2/4+m*penalty k d)

theorem powers_mono (m M : ℝ) (hm : 0 ≤ m) (h : m ≤ M) : m^2 ≤ M^2 ∧ m^3 ≤ M^3 := by
  have hM : 0 ≤ M := hm.trans h
  have h2 := mul_nonneg (sub_nonneg.mpr h) (add_nonneg hM hm)
  have h3 := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ M^2+M*m+m^2 by positivity)
  constructor <;> nlinarith

theorem P_antitone (k m M : ℝ) (hm : 0 ≤ m) (h : m ≤ M) : P k M ≤ P k m := by
  have hs := powers_mono m M hm h
  have hc : 0 ≤ 9*k^2-12*k+24 := by nlinarith [sq_nonneg (3*k-2)]
  have hp := mul_nonneg (sub_nonneg.mpr h) hc
  unfold P
  nlinarith only [hs.1,hs.2,hp]

theorem Q_antitone (k m M : ℝ) (hm : 0 ≤ m) (h : m ≤ M) : Q k M ≤ Q k m := by
  have hs := powers_mono m M hm h
  unfold Q
  nlinarith only [h,hs.1,hs.2]

theorem P_positive (k m : ℝ) (hk : 43 ≤ k) (hm : 0 ≤ m) (hM : m ≤ (k+5)/3) : 0 ≤ P k m := by
  have hmono := P_antitone k m ((k+5)/3) hm hM
  have hid : 9*P k ((k+5)/3) =
      8*(k-43)^3+690*(k-43)^2+15057*(k-43)+6912 := by unfold P; ring
  have hh : 0 ≤ k-43 := by linarith
  have hpos : 0 ≤ 8*(k-43)^3+690*(k-43)^2+15057*(k-43)+6912 := by positivity
  linarith

theorem Q_positive (k m : ℝ) (hk : 17 ≤ k) (hm : 0 ≤ m) (hM : m ≤ (k+2)/2) : 0 ≤ Q k m := by
  have hmono := Q_antitone k m ((k+2)/2) hm hM
  have hid : 8*Q k ((k+2)/2) =
      5*(k-17)^3+177*(k-17)^2+1615*(k-17)+747 := by unfold Q; ring
  have hh : 0 ≤ k-17 := by linarith
  have hpos : 0 ≤ 5*(k-17)^3+177*(k-17)^2+1615*(k-17)+747 := by positivity
  linarith

theorem penalty_low (k d : ℝ) (hk : 0 ≤ k) (hd : d ≤ k/4) : penalty k d = 0 := by
  unfold penalty
  rw [max_eq_left (show max (d/2-k/8) (d-k/2) ≤ 0 by apply max_le <;> linarith)]

theorem penalty_middle (k d : ℝ) (hl : k/4 ≤ d) (hu : d ≤ 3*k/4) :
    penalty k d = d/2-k/8 := by
  unfold penalty
  rw [max_eq_left (by linarith : d-k/2 ≤ d/2-k/8),max_eq_right (by linarith)]

theorem penalty_high (k d : ℝ) (hk : 0 ≤ k) (hd : 3*k/4 ≤ d) :
    penalty k d = d-k/2 := by
  unfold penalty
  rw [max_eq_right (by linarith : d/2-k/8 ≤ d-k/2),max_eq_right (by linarith)]

theorem middle_identity (k d m : ℝ) (hl : k/4 ≤ d) (hu : d ≤ 3*k/4) :
    48*F k d m = P k m+3*m*(4*d-k-m-2)^2 := by
  unfold F P
  rw [penalty_middle k d hl hu]
  ring

theorem high_identity (k d m : ℝ) (hk : 0 ≤ k) (hd : 3*k/4 ≤ d) :
    12*F k d m = Q k m+3*m*(2*d-k-m-1)^2 := by
  unfold F Q
  rw [penalty_high k d hk hd]
  ring

theorem small_mass_F (k d m : ℝ) (hk : 43 ≤ k) (hd : k/4 ≤ d)
    (hm : 0 ≤ m) (hM : m ≤ (k+5)/3) : 0 ≤ F k d m := by
  by_cases hu : d ≤ 3*k/4
  · have hid := middle_identity k d m hd hu
    have hP := P_positive k m hk hm hM
    have hsq : 0 ≤ 3*m*(4*d-k-m-2)^2 := by positivity
    linarith
  · have hid := high_identity k d m (by linarith) (le_of_not_ge hu)
    have hQ := Q_positive k m (by linarith) hm (by linarith)
    have hsq : 0 ≤ 3*m*(2*d-k-m-1)^2 := by positivity
    linarith

/-- The one-type scalar comparison uses only the four displayed lower bounds. -/
theorem single_type (k d r c v : ℝ) (hk : 43 ≤ k) (hr : 0 ≤ r)
    (hc : c ≤ (k-1)^2/4)
    (hclique : (k-1)*(k-2)/3 ≤ v)
    (hout : r*(d-1) ≤ v)
    (hcomplete : 2*c+2*r*(d-1) ≤ 3*v)
    (hall : k*(k-1)*(k-2)/3+r*d*(d-1) ≤ (k+r)*v) :
    c+r*penalty k d ≤ v := by
  by_cases hd : d ≤ k/4
  · rw [penalty_low k d (by linarith) hd,mul_zero,add_zero]
    have hprod : 0 ≤ (k-1)*(k-5) := mul_nonneg (by linarith) (by linarith)
    nlinarith only [hc,hclique,hprod]
  · have hd' : k/4 ≤ d := le_of_not_ge hd
    by_cases hmid : d ≤ 3*k/4
    · rw [penalty_middle k d hd' hmid]
      by_cases hrlarge : (k+5)/3 ≤ r
      · have hprod := mul_nonneg (sub_nonneg.mpr hrlarge) (show 0 ≤ k-4 by linarith)
        nlinarith only [hk,hc,hclique,hcomplete,hprod]
      · have hF := small_mass_F k d r hk hd' hr (le_of_not_ge hrlarge)
        unfold F at hF
        rw [penalty_middle k d hd' hmid] at hF
        have hpos : 0 < k+r := by linarith
        by_contra hh
        have hp := mul_pos hpos (sub_pos.mpr (lt_of_not_ge hh))
        nlinarith only [hF,hall,hc,hp,
          mul_nonneg hpos.le (sub_nonneg.mpr hc)]
    · rw [penalty_high k d (by linarith) (le_of_not_ge hmid)]
      by_cases hrlarge : (k+2)/2 ≤ r
      · have hprod := mul_nonneg (sub_nonneg.mpr hrlarge) (show 0 ≤ k/2-1 by linarith)
        nlinarith only [hk,hc,hout,hprod]
      · have hid := high_identity k d r (by linarith) (le_of_not_ge hmid)
        have hQ := Q_positive k r (by linarith) hr (le_of_not_ge hrlarge)
        have hsq : 0 ≤ 3*r*(2*d-k-r-1)^2 := by positivity
        have hF : 0 ≤ F k d r := by linarith
        unfold F at hF
        rw [penalty_high k d (by linarith) (le_of_not_ge hmid)] at hF
        have hpos : 0 < k+r := by linarith
        by_contra hh
        have hp := mul_pos hpos (sub_pos.mpr (lt_of_not_ge hh))
        nlinarith only [hF,hall,hp,mul_nonneg hpos.le (sub_nonneg.mpr hc)]

/-- Small total multiplicity is handled by a weighted polynomial identity. -/
theorem small_total_mass (k s t p q c v : ℝ) (hk : 43 ≤ k)
    (hs : k/4 ≤ s) (ht : k/4 ≤ t) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hm : 3*(p+q) ≤ k+5) (hc : c ≤ (k-1)^2/4)
    (hall : k*(k-1)*(k-2)/3+p*s*(s-1)+q*t*(t-1) ≤ (k+p+q)*v) :
    c+p*penalty k s+q*penalty k t ≤ v := by
  have hFs := small_mass_F k s (p+q) hk hs (add_nonneg hp hq) (by linarith)
  have hFt := small_mass_F k t (p+q) hk ht (add_nonneg hp hq) (by linarith)
  by_cases hz : p+q = 0
  · have hp0 : p = 0 := by linarith
    have hq0 : q = 0 := by linarith
    subst p; subst q
    simp only [zero_mul,add_zero] at *
    have hpos : 0 < k := by linarith
    have hgap := mul_nonneg (show 0 ≤ k-1 by linarith) (show 0 ≤ k-5 by linarith)
    by_contra h
    have hprod := mul_pos hpos (sub_pos.mpr (lt_of_not_ge h))
    have hup := mul_nonneg hpos.le (sub_nonneg.mpr hc)
    have hgapK := mul_nonneg hpos.le hgap
    nlinarith only [hall,hprod,hup,hgapK]
  · have hmpos : 0 < p+q := by
      by_contra hh
      exact hz (by linarith)
    have hweighted := add_nonneg (mul_nonneg hp hFs) (mul_nonneg hq hFt)
    have hid : p*F k s (p+q)+q*F k t (p+q) = (p+q)*
        (k*(k-1)*(k-2)/3+p*s*(s-1)+q*t*(t-1)-
          (k+p+q)*((k-1)^2/4+p*penalty k s+q*penalty k t)) := by unfold F; ring
    rw [hid] at hweighted
    have hbr : 0 ≤ k*(k-1)*(k-2)/3+p*s*(s-1)+q*t*(t-1)-
        (k+p+q)*((k-1)^2/4+p*penalty k s+q*penalty k t) := by
      by_contra hn
      have hmneg := mul_neg_of_pos_of_neg hmpos (lt_of_not_ge hn)
      exact (not_lt_of_ge hweighted) hmneg
    have hkpos : 0 < k+p+q := by linarith
    by_contra h
    have hprod := mul_pos hkpos (sub_pos.mpr (lt_of_not_ge h))
    have hup := mul_nonneg hkpos.le (sub_nonneg.mpr hc)
    nlinarith only [hbr,hall,hprod,hup]

#print axioms P_positive
#print axioms Q_positive
#print axioms small_mass_F
#print axioms single_type
#print axioms small_total_mass
#check small_total_mass
end TuzaAnalytic

/-! Integer bounds used in the finite certificate. -/
namespace TuzaFiniteInterfaces
open Finset TuzaCompression TuzaGraphCompression TuzaMatchingClasses
  TuzaIndependentAllocation TuzaCoupledAllocation TuzaCoreCompletion TuzaGraphBounds
  TuzaBalancedRounding TuzaSeparableCover TuzaRegionCuts TuzaCoverCompression
  TuzaRealBounds TuzaPackingInterfaces
variable {V : Type*} [DecidableEq V] [Fintype V]

def ceilDiv (a b : ℕ) : ℕ := (a+b-1)/b

theorem ceilDiv_le (a b l : ℕ) (hb : 0 < b) (h : a ≤ b*l) : ceilDiv a b ≤ l := by
  have hd := Nat.div_add_mod (a+b-1) b
  by_contra hn
  have hlt : l+1 ≤ (a+b-1)/b := by unfold ceilDiv at hn; omega
  have hm := Nat.mul_le_mul_left b hlt
  rw [Nat.mul_add,Nat.mul_one] at hm
  omega

def outsideI (s t u p q : ℕ) : ℕ :=
  ceilDiv (colorCount t*p*s.choose 2+colorCount s*q*t.choose 2-p*q*u.choose 2)
    (colorCount s*colorCount t)
def outsideC (s t u p q : ℕ) : ℕ :=
  ceilDiv (p*s.choose 2+q*t.choose 2-(p+q-colorCount t)*u.choose 2) (colorCount t)
def outsideLower (s t u p q : ℕ) : ℕ := max (outsideI s t u p q) (outsideC s t u p q)

theorem independent_integer_witness (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card)
    (p q : ℕ) (hp : p ≤ colorCount S.card) (hq : q ≤ colorCount T.card) :
    ∃ P : Finset (Finset (V ⊕ (Fin p ⊕ Fin q))),
      IsPacking (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) P ∧
      outsideI S.card T.card (S ∩ T).card p q ≤ P.card ∧
      ∀ t ∈ P, t.toRight.Nonempty := by
  obtain ⟨P,hP,hb,hout⟩ := independent_allocation (⊤ : SimpleGraph V) S T hs ht
    (by intro a ha b hb hab; exact hab) (by intro a ha b hb hab; exact hab) p q
  rw [min_eq_left hp,min_eq_left hq] at hb
  refine ⟨P,hP,ceilDiv_le _ _ _ (Nat.mul_pos (palette_bounds _ hs).1 (palette_bounds _ ht).1) ?_,hout⟩
  omega

theorem coupled_integer_witness (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card)
    (hst : S.card ≤ T.card) (p q : ℕ)
    (hp : p ≤ colorCount S.card) (hq : q ≤ colorCount T.card) :
    ∃ P : Finset (Finset (V ⊕ (Fin p ⊕ Fin q))),
      IsPacking (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) P ∧
      outsideC S.card T.card (S ∩ T).card p q ≤ P.card ∧
      ∀ t ∈ P, t.toRight.Nonempty := by
  obtain ⟨P,hP,hb,hout⟩ := coupled_allocation (⊤ : SimpleGraph V) S T hs ht
    (by intro a ha b hb hab; exact hab) (by intro a ha b hb hab; exact hab) p q
  have hpT := hp.trans (palette_mono _ _ hst)
  rw [max_eq_right hst,min_eq_left hpT,min_eq_left hq] at hb
  refine ⟨P,hP,ceilDiv_le _ _ _ (palette_bounds _ ht).1 ?_,hout⟩
  omega

theorem integer_outside_witness (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card)
    (hst : S.card ≤ T.card) (p q : ℕ)
    (hp : p ≤ colorCount S.card) (hq : q ≤ colorCount T.card) :
    ∃ P : Finset (Finset (V ⊕ (Fin p ⊕ Fin q))),
      IsPacking (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) P ∧
      outsideLower S.card T.card (S ∩ T).card p q ≤ P.card ∧
      ∀ t ∈ P, t.toRight.Nonempty := by
  unfold outsideLower
  by_cases h : outsideI S.card T.card (S ∩ T).card p q ≤ outsideC S.card T.card (S ∩ T).card p q
  · rw [max_eq_right h]
    exact coupled_integer_witness S T hs ht hst p q hp hq
  · rw [max_eq_left (le_of_not_ge h)]
    exact independent_integer_witness S T hs ht p q hp hq

def averageLower (k s t r z : ℕ) : ℕ :=
  ceilDiv (k.choose 3+r*s.choose 2+z*t.choose 2) (k+r+z)

def packingLower (k s t u p q : ℕ) : ℕ :=
  max (ceilDiv (k.choose 3) k)
    (max (outsideLower s t u p q)
      (max (ceilDiv (coreBudget k+2*outsideLower s t u p q) 3)
        (max (averageLower k s t p q)
          (max (averageLower k s t p 0) (averageLower k s t 0 q)))))

theorem packingLower_sound (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card)
    (hst : S.card ≤ T.card) (p q : ℕ)
    (hp : p ≤ colorCount S.card) (hq : q ≤ colorCount T.card) :
    packingLower (Fintype.card V) S.card T.card (S ∩ T).card p q ≤
      packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by
  let k := Fintype.card V
  let nu := packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q))
  let ell := outsideLower S.card T.card (S ∩ T).card p q
  have hk : 2 ≤ k := hs.trans (card_le_univ S)
  have havg (r z : ℕ) (hr : r ≤ p) (hz : z ≤ q) : averageLower k S.card T.card r z ≤ nu := by
    apply ceilDiv_le _ _ _ (by omega)
    exact subgraph_triangle_bound S T r z p q hr hz
  have hclique : ceilDiv (k.choose 3) k ≤ nu := by
    have h := subgraph_triangle_bound S T 0 0 p q (Nat.zero_le _) (Nat.zero_le _)
    simp only [zero_mul,Nat.add_zero] at h
    exact ceilDiv_le _ _ _ (by omega) h
  obtain ⟨P,hP,hPe,hout⟩ := integer_outside_witness S T hs ht hst p q hp hq
  have hcomp := core_completion_bound (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q))
    (by intro a b h; exact h) (by intro a b h; exact h) P hP hout
  have hell : ell ≤ nu := hPe.trans hcomp.1
  have hcompletion : ceilDiv (coreBudget k+2*ell) 3 ≤ nu := by
    apply ceilDiv_le _ _ _ (by decide)
    have hid : coreBudget k+k^2/4 = k.choose 2 := Nat.sub_add_cancel (core_floor_le k hk)
    have hc := hcomp.2
    change 2*P.card+k.choose 2 ≤ 3*nu+k^2/4 at hc
    change ell ≤ P.card at hPe
    omega
  exact max_le hclique (max_le hell (max_le hcompletion
    (max_le (havg p q le_rfl le_rfl)
      (max_le (havg p 0 le_rfl (Nat.zero_le _)) (havg 0 q (Nat.zero_le _) le_rfl)))))

def penalty8 (k d : ℕ) : ℕ := max (4*d-k) (8*d-4*k)
def separableUpper (k s t p q : ℕ) : ℕ :=
  (8*coreBudget k+p*penalty8 k s+q*penalty8 k t)/8

set_option maxHeartbeats 800000 in
theorem penalty8_real (k d : ℕ) : (penalty8 k d : ℝ) = 8*penalty k d := by
  have hmax (a b : ℕ) : ((max a b : ℕ) : ℝ) = max (a : ℝ) (b : ℝ) := by
    by_cases h : a ≤ b
    · rw [max_eq_right h,max_eq_right (by exact_mod_cast h)]
    · rw [max_eq_left (le_of_not_ge h),max_eq_left (by exact_mod_cast le_of_not_ge h)]
  unfold penalty8
  rw [hmax,cast_sub_max,cast_sub_max]
  push_cast
  unfold penalty
  simp only [max_def]
  split_ifs <;> linarith

theorem separableUpper_sound (S T : Finset V) (p q : ℕ) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      separableUpper (Fintype.card V) S.card T.card p q := by
  have hb := separable_cover_bound S T p q
  have hs := penalty8_real (Fintype.card V) S.card
  have ht := penalty8_real (Fintype.card V) T.card
  have hR : (8 : ℝ)*(coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q))) ≤
      8*(coreBudget (Fintype.card V) : ℝ)+(p : ℝ)*penalty8 (Fintype.card V) S.card+
      (q : ℝ)*penalty8 (Fintype.card V) T.card := by
    rw [hs,ht]
    nlinarith only [hb]
  have hN : 8*coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      8*coreBudget (Fintype.card V)+p*penalty8 (Fintype.card V) S.card+
      q*penalty8 (Fintype.card V) T.card := by exact_mod_cast hR
  unfold separableUpper
  omega

#print axioms ceilDiv_le
#print axioms integer_outside_witness
#print axioms packingLower_sound
#print axioms penalty8_real
#print axioms separableUpper_sound
#check separableUpper_sound
end TuzaFiniteInterfaces

/-! Arbitrary split-graph coordinates and removal of inactive outer vertices. -/
namespace TuzaRepresentation
open Finset TuzaCompression TuzaGraphCompression TuzaGraphTransfer TuzaCutCovers
  TuzaIndependentAllocation TuzaCoreCompletion TuzaCoverCompression
variable {V W C : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq C]

theorem triangle_preimage [Fintype V] (H : SimpleGraph V) (G : SimpleGraph W)
    (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ a b, H.Adj a b ↔ G.Adj (f a) (f b))
    (t : Finset W) (ht : G.IsNClique 3 t)
    (hrange : ∀ w ∈ t, ∃ v, f v = w) : ∃ u, H.IsNClique 3 u ∧ u.image f = t := by
  let u := univ.filter (fun v => f v ∈ t)
  have he : u.image f = t := by
    ext w
    constructor
    · rintro hw
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hw
      exact (mem_filter.mp hv).2
    · intro hw
      obtain ⟨v,rfl⟩ := hrange w hw
      exact mem_image.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,hw⟩,rfl⟩
  refine ⟨u,⟨?_,?_⟩,he⟩
  · intro a ha b hb hab
    exact (hadj a b).mpr (ht.isClique (mem_filter.mp ha).2 (mem_filter.mp hb).2
      (fun h => hab (hf h)))
  · have hc := card_image_of_injective u hf
    rw [he,ht.card_eq] at hc
    exact hc.symm

def partitionEquiv (K : Finset V) : ({v // v ∈ K} ⊕ {v // v ∉ K}) ≃ V where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun v := if h : v ∈ K then .inl ⟨v,h⟩ else .inr ⟨v,h⟩
  left_inv a := by cases a with
    | inl a => simp [a.property]
    | inr a => simp [a.property]
  right_inv v := by by_cases h : v ∈ K <;> simp [h]

noncomputable def neighbors [Fintype V] (G : SimpleGraph V) (K : Finset V)
    (c : {v // v ∉ K}) : Finset {v // v ∈ K} := by
  classical
  exact univ.filter (fun v => G.Adj v.val c.val)

theorem partition_adjacency [Fintype V] (G : SimpleGraph V) (K : Finset V)
    (hK : G.IsClique K) (hI : ∀ a ∉ K, ∀ b ∉ K, ¬G.Adj a b)
    (a b : {v // v ∈ K} ⊕ {v // v ∉ K}) :
    (splitGraph (neighbors G K)).Adj a b ↔ G.Adj (partitionEquiv K a) (partitionEquiv K b) := by
  classical
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change (a ≠ b) ↔ G.Adj a.val b.val
      constructor
      · intro h
        exact hK a.property b.property (fun he => h (Subtype.ext he))
      · intro h he
        subst b
        exact G.loopless.irrefl a.val h
    | inr b => simp [splitGraph,neighbors,partitionEquiv]
  | inr a =>
    cases b with
    | inl b =>
      change b ∈ neighbors G K a ↔ G.Adj a.val b.val
      simp only [neighbors,mem_filter,mem_univ,true_and]
      exact G.adj_comm _ _
    | inr b =>
      change False ↔ G.Adj a.val b.val
      exact iff_of_false (by simp) (hI a.val a.property b.val b.property)

abbrev First (N : C → Finset V) (S : Finset V) := {c // N c = S}
abbrev Second (N : C → Finset V) (S T : Finset V) := {c // N c ≠ S ∧ N c = T}

def typeMap (N : C → Finset V) (S T : Finset V) :
    V ⊕ (First N S ⊕ Second N S T) → V ⊕ C :=
  Sum.map id (Sum.elim Subtype.val Subtype.val)

theorem typeMap_injective (N : C → Finset V) (S T : Finset V) :
    Function.Injective (typeMap N S T) := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (Sum.inl.inj h)
    | inr b => cases h
  | inr a => cases b with
    | inl b => cases h
    | inr b =>
      have hh := Sum.inr.inj h
      cases a with
      | inl a => cases b with
        | inl b => exact congrArg Sum.inr (congrArg Sum.inl (Subtype.ext hh))
        | inr b =>
          have ha := a.property
          have hb := b.property.1
          change a.val = b.val at hh
          rw [hh] at ha
          exact False.elim (hb ha)
      | inr a => cases b with
        | inl b =>
          have ha := a.property.1
          have hb := b.property
          change a.val = b.val at hh
          rw [← hh] at hb
          exact False.elim (ha hb)
        | inr b => exact congrArg Sum.inr (congrArg Sum.inr (Subtype.ext hh))

theorem typeMap_adjacency (N : C → Finset V) (S T : Finset V)
    (a b : V ⊕ (First N S ⊕ Second N S T)) :
    (twoAttached (⊤ : SimpleGraph V) S T (First N S) (Second N S T)).Adj a b ↔
      (splitGraph N).Adj (typeMap N S T a) (typeMap N S T b) := by
  cases a with
  | inl a => cases b with
    | inl b => rfl
    | inr b => cases b with
      | inl b => simp [twoAttached,neighborhood,typeMap,splitGraph,b.property]
      | inr b => simp [twoAttached,neighborhood,typeMap,splitGraph,b.property.2]
  | inr a => cases b with
    | inl b => cases a with
      | inl a => simp [twoAttached,neighborhood,typeMap,splitGraph,a.property]
      | inr a => simp [twoAttached,neighborhood,typeMap,splitGraph,a.property.2]
    | inr b => rfl

theorem triangle_in_active_range (N : C → Finset V) (S T : Finset V)
    (htypes : ∀ c, 2 ≤ (N c).card → N c = S ∨ N c = T)
    (t : Finset (V ⊕ C)) (ht : (splitGraph N).IsNClique 3 t) :
    ∀ w ∈ t, ∃ v, typeMap N S T v = w := by
  intro w hw
  cases w with
  | inl v => exact ⟨Sum.inl v,rfl⟩
  | inr c =>
    have hc : t.toLeft.card = 2 := centered_left_card (splitGraph N)
      (by intro c d h; exact h) ht ⟨c,mem_toRight.mpr hw⟩
    have hs : t.toLeft ⊆ N c := by
      intro v hv
      exact ht.isClique (mem_toLeft.mp hv) hw (by simp)
    have hactive : 2 ≤ (N c).card := by rw [← hc]; exact card_le_card hs
    by_cases hfirst : N c = S
    · exact ⟨Sum.inr (Sum.inl ⟨c,hfirst⟩),rfl⟩
    · have hsecond := (htypes c hactive).resolve_left hfirst
      exact ⟨Sum.inr (Sum.inr ⟨c,hfirst,hsecond⟩),rfl⟩

/-- Low-degree outside vertices create no additional triangle obligation. -/
theorem remove_inactive [Fintype V] [Fintype C] (N : C → Finset V) (S T : Finset V)
    (htypes : ∀ c, 2 ≤ (N c).card → N c = S ∨ N c = T)
    (hTuza : coverNumber (twoAttached (⊤ : SimpleGraph V) S T (First N S) (Second N S T)) ≤
      2*packingNumber (twoAttached (⊤ : SimpleGraph V) S T (First N S) (Second N S T))) :
    coverNumber (splitGraph N) ≤ 2*packingNumber (splitGraph N) := by
  apply tuza_transfer _ _ (typeMap N S T) (typeMap_injective N S T)
    (fun a b h => (typeMap_adjacency N S T a b).mp h) ?_ hTuza
  intro t ht
  exact triangle_preimage _ _ (typeMap N S T) (typeMap_injective N S T)
    (typeMap_adjacency N S T) t ht (triangle_in_active_range N S T htypes t ht)


theorem finite_centers [Fintype V] [Fintype C] {D : Type*} [DecidableEq D] [Fintype D]
    (S T : Finset V) :
    packingNumber (twoAttached (⊤ : SimpleGraph V) S T C D) =
      packingNumber (twoAttached (⊤ : SimpleGraph V) S T
        (Fin (Fintype.card C)) (Fin (Fintype.card D))) ∧
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T C D) =
      coverNumber (twoAttached (⊤ : SimpleGraph V) S T
        (Fin (Fintype.card C)) (Fin (Fintype.card D))) := by
  let e := Equiv.sumCongr (Equiv.refl V)
    (Equiv.sumCongr (Fintype.equivFin C) (Fintype.equivFin D))
  apply iso_parameters _ _ e
  intro a b
  cases a with
  | inl a => cases b with
    | inl b => rfl
    | inr b => cases b <;> rfl
  | inr a => cases b with
    | inl b => cases a <;> rfl
    | inr b => rfl

/-- A theorem for two finite center families transfers to an arbitrary split graph. -/
theorem split_from_fin [Fintype V] (G : SimpleGraph V) (K : Finset V)
    (hK : G.IsClique K) (hI : ∀ a ∉ K, ∀ b ∉ K, ¬G.Adj a b)
    (S T : Finset {v // v ∈ K})
    (htypes : ∀ c, 2 ≤ (neighbors G K c).card → neighbors G K c = S ∨ neighbors G K c = T)
    (hfin : ∀ p q : ℕ,
      coverNumber (twoAttached (⊤ : SimpleGraph {v // v ∈ K}) S T (Fin p) (Fin q)) ≤
        2*packingNumber (twoAttached (⊤ : SimpleGraph {v // v ∈ K}) S T (Fin p) (Fin q))) :
    coverNumber G ≤ 2*packingNumber G := by
  classical
  have hi := iso_parameters (splitGraph (neighbors G K)) G (partitionEquiv K)
    (partition_adjacency G K hK hI)
  rw [← hi.1,← hi.2]
  apply remove_inactive (neighbors G K) S T htypes
  have hc := finite_centers (C := First (neighbors G K) S) (D := Second (neighbors G K) S T) S T
  rw [hc.1,hc.2]
  exact hfin _ _

#print axioms finite_centers
#print axioms split_from_fin
#print axioms triangle_preimage
#print axioms partition_adjacency
#print axioms typeMap_injective
#print axioms typeMap_adjacency
#print axioms triangle_in_active_range
#print axioms remove_inactive
#check remove_inactive
end TuzaRepresentation


/-! Graph forms of the analytic reductions. -/
namespace TuzaGraphReductions
open Finset TuzaCompression TuzaGraphCompression TuzaIndependentAllocation TuzaGraphBounds
  TuzaBalancedRounding TuzaCommonRounding TuzaPackingInterfaces TuzaCoreCompletion
  TuzaSeparableCover TuzaRegionCuts TuzaGraphTransfer TuzaCoverCompression TuzaAnalytic
variable {V : Type*} [DecidableEq V] [Fintype V]

theorem choose_three_real (n : ℕ) : (n.choose 3 : ℝ) = (n : ℝ)*((n : ℝ)-1)*((n : ℝ)-2)/6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hc : (n+1).choose 3 = n.choose 2+n.choose 3 := Nat.choose_succ_succ' n 2
    simp only [Nat.succ_eq_add_one,hc,Nat.cast_add,Nat.cast_one,choose_two_real,ih]
    ring

theorem square_floor_bounds (k : ℕ) : 4*(k^2/4) ≤ k^2 ∧ k^2 ≤ 4*(k^2/4)+1 := by
  let r := k/2
  have hk : k = 2*r ∨ k = 2*r+1 := by omega
  rcases hk with hk | hk
  · rw [hk,show (2*r)^2 = (r*r)*4 by ring]
    omega
  · rw [hk,show (2*r+1)^2 = (r*(r+1))*4+1 by ring]
    omega

theorem coreBudget_bounds (k : ℕ) (hk : 2 ≤ k) :
    (k : ℝ)*((k : ℝ)-2)/4 ≤ (coreBudget k : ℝ) ∧
      (coreBudget k : ℝ) ≤ ((k : ℝ)-1)^2/4 := by
  have hid : coreBudget k+k^2/4 = k.choose 2 := Nat.sub_add_cancel (core_floor_le k hk)
  have hR : (coreBudget k : ℝ)+((k^2/4 : ℕ) : ℝ) = (k.choose 2 : ℝ) := by exact_mod_cast hid
  rw [choose_two_real] at hR
  have h0 : (4 : ℝ)*((k^2/4 : ℕ) : ℝ) ≤ (k : ℝ)^2 := by exact_mod_cast (square_floor_bounds k).1
  have h1 : (k : ℝ)^2 ≤ 4*((k^2/4 : ℕ) : ℝ)+1 := by exact_mod_cast (square_floor_bounds k).2
  constructor <;> nlinarith only [hR,h0,h1]

theorem clique_real (S T : Finset V) (p q : ℕ) (hk : 0 < Fintype.card V) :
    ((Fintype.card V : ℝ)-1)*((Fintype.card V : ℝ)-2)/3 ≤
      2*(packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) := by
  have hn := subgraph_triangle_bound S T 0 0 p q (Nat.zero_le _) (Nat.zero_le _)
  simp only [zero_mul,Nat.add_zero] at hn
  have hR : ((Fintype.card V).choose 3 : ℝ) ≤ (Fintype.card V : ℝ)*
      packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by exact_mod_cast hn
  rw [choose_three_real] at hR
  have hpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast hk
  by_contra h
  have hp := mul_pos hpos (sub_pos.mpr (lt_of_not_ge h))
  nlinarith only [hR,hp]

theorem all_triangles_real (S T : Finset V) (p q : ℕ) :
    (Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)*((Fintype.card V : ℝ)-2)/3+
      (p : ℝ)*S.card*((S.card : ℝ)-1)+(q : ℝ)*T.card*((T.card : ℝ)-1) ≤
      ((Fintype.card V : ℝ)+p+q)*
        (2*(packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ)) := by
  have hn := triangle_count_bound (C := Fin p) (D := Fin q) S T
  simp only [Fintype.card_fin] at hn
  have hR : ((Fintype.card V).choose 3 : ℝ)+(p : ℝ)*S.card.choose 2+(q : ℝ)*T.card.choose 2 ≤
      ((Fintype.card V : ℝ)+p+q)*packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by exact_mod_cast hn
  rw [choose_three_real,choose_two_real,choose_two_real] at hR
  nlinarith only [hR]

theorem independent_zero (s t u p : ℕ) (hs : 0 < s) :
    2*independentRate s t u p 0 = (p : ℝ)*((s : ℝ)-1) := by
  unfold independentRate
  simp only [Nat.cast_zero,zero_div,zero_mul,mul_zero,add_zero,sub_zero]
  rw [choose_two_real]
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  field_simp [hsR]
  <;> ring

theorem single_type_graph (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card)
    (p : ℕ) (hp : p ≤ colorCount S.card) (hk : 43 ≤ Fintype.card V) :
    (coreBudget (Fintype.card V) : ℝ)+(p : ℝ)*penalty (Fintype.card V) S.card ≤
      2*(packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin 0)) : ℝ) := by
  obtain ⟨P,hP,hb,hout⟩ := independent_witness S T hs ht p 0 hp (Nat.zero_le _)
  have hi := independent_zero S.card T.card (S ∩ T).card p (by omega)
  have hc := core_completion_bound (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin 0))
    (by intro a b h; exact h) (by intro a b h; exact h) P hP hout
  have hPnum : (P.card : ℝ) ≤ packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin 0)) := by exact_mod_cast hc.1
  have hCnum : 2*(P.card : ℝ)+(Fintype.card V).choose 2 ≤
      3*(packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin 0)) : ℝ)+
        ((Fintype.card V^2/4 : ℕ) : ℝ) := by exact_mod_cast hc.2
  have hcoreN : coreBudget (Fintype.card V)+Fintype.card V^2/4 = (Fintype.card V).choose 2 :=
    Nat.sub_add_cancel (core_floor_le _ (by omega))
  have hcoreR : (coreBudget (Fintype.card V) : ℝ)+((Fintype.card V^2/4 : ℕ) : ℝ) =
      ((Fintype.card V).choose 2 : ℝ) := by exact_mod_cast hcoreN
  apply single_type (Fintype.card V) S.card p (coreBudget (Fintype.card V))
  · exact_mod_cast hk
  · positivity
  · exact (coreBudget_bounds _ (by omega)).2
  · exact clique_real S T p 0 (by omega)
  · nlinarith only [hi,hb,hPnum]
  · nlinarith only [hi,hb,hCnum,hcoreR]
  · simpa only [Nat.cast_zero,zero_mul,add_zero] using all_triangles_real S T p 0

theorem small_neighborhood (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card)
    (p q : ℕ) (hq : q ≤ colorCount T.card) (hk : 43 ≤ Fintype.card V)
    (hsmall : (S.card : ℝ) ≤ (Fintype.card V : ℝ)/4) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      2*packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by
  have hcover := separable_cover_bound S T p q
  rw [penalty_low _ _ (by positivity) hsmall,mul_zero,add_zero] at hcover
  have hsingle := single_type_graph T S ht hs q hq hk
  have hswap := swap_types S T 0 q
  rw [← hswap.1] at hsingle
  have hmono := two_type_monotone S T 0 q p q (Nat.zero_le _) le_rfl
  have hR : (packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin 0) (Fin q)) : ℝ) ≤
      packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by exact_mod_cast hmono
  have h : (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) ≤
      2*(packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) := by linarith
  exact_mod_cast h

theorem small_multiplicity (S T : Finset V) (p q : ℕ) (hk : 43 ≤ Fintype.card V)
    (hs : (Fintype.card V : ℝ)/4 ≤ S.card) (ht : (Fintype.card V : ℝ)/4 ≤ T.card)
    (hm : 3*(p+q) ≤ Fintype.card V+5) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      2*packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by
  have hscalar := small_total_mass (Fintype.card V) S.card T.card p q
    (coreBudget (Fintype.card V))
    (2*(packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ))
    (by exact_mod_cast hk) hs ht (by positivity) (by positivity) (by exact_mod_cast hm)
    (coreBudget_bounds _ (by omega)).2 (all_triangles_real S T p q)
  have hcover := separable_cover_bound S T p q
  have h := hcover.trans hscalar
  exact_mod_cast h


theorem small_both_neighborhoods (S T : Finset V) (p q : ℕ)
    (hk : 43 ≤ Fintype.card V) (hst : S.card ≤ T.card)
    (ht : (T.card : ℝ) ≤ (Fintype.card V : ℝ)/2) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      2*packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by
  have ht2 : 2*T.card ≤ Fintype.card V := by
    exact_mod_cast (show 2*(T.card : ℝ) ≤ (Fintype.card V : ℝ) by linarith)
  have hcover := small_shadow S T p q (by omega) hst (by omega)
  have hR : (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) ≤
      (coreBudget (Fintype.card V) : ℝ)+((S \ T).card : ℝ)*(S ∩ T).card := by exact_mod_cast hcover
  have hsum : ((S \ T).card : ℝ)+(S ∩ T).card = (S.card : ℝ) := by
    exact_mod_cast card_sdiff_add_card_inter S T
  have hstR : (S.card : ℝ) ≤ T.card := by exact_mod_cast hst
  have hkR : (43 : ℝ) ≤ Fintype.card V := by exact_mod_cast hk
  have ha : (0 : ℝ) ≤ (S \ T).card := by positivity
  have hu : (0 : ℝ) ≤ (S ∩ T).card := by positivity
  have hprod := mul_nonneg
    (show 0 ≤ (Fintype.card V : ℝ)/2-((S \ T).card : ℝ)-(S ∩ T).card by linarith)
    (show 0 ≤ (Fintype.card V : ℝ)/2+((S \ T).card : ℝ)+(S ∩ T).card by positivity)
  have hsquare := sq_nonneg (((S \ T).card : ℝ)-(S ∩ T).card)
  have hgap := mul_nonneg (show 0 ≤ (Fintype.card V : ℝ)-24 by linarith)
    (show 0 ≤ (Fintype.card V : ℝ) by positivity)
  have hclique := clique_real S T p q (by omega)
  have hcup := (coreBudget_bounds (Fintype.card V) (by omega)).2
  have hfinal : (coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) ≤
      2*(packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) : ℝ) := by
    nlinarith only [hR,hprod,hsquare,hgap,hclique,hcup]
  exact_mod_cast hfinal

theorem zero_second_type (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card)
    (p : ℕ) (hp : p ≤ colorCount S.card) (hk : 43 ≤ Fintype.card V) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin 0)) ≤
      2*packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin 0)) := by
  have hcover := separable_cover_bound S T p 0
  simp only [Nat.cast_zero,zero_mul,add_zero] at hcover
  have h := hcover.trans (single_type_graph S T hs ht p hp hk)
  exact_mod_cast h

#print axioms small_both_neighborhoods
#print axioms zero_second_type
#print axioms choose_three_real
#print axioms coreBudget_bounds
#print axioms clique_real
#print axioms all_triangles_real
#print axioms single_type_graph
#print axioms small_neighborhood
#print axioms small_multiplicity
#check small_multiplicity
end TuzaGraphReductions


/-! Polynomial comparison for the common-neighborhood certificate shortcut. -/
namespace TuzaNormalizedScalar
noncomputable def B (m r : ℝ) : ℝ :=
  1/12+m^2/4-(1+m^2)*r/2+(5/12-m/2)*r^2

theorem common_margin (m r : ℝ) (hm : 0 ≤ m ∧ m ≤ 2) (hr : 0 ≤ r ∧ r ≤ 1/34) :
    (1+3*m^2)/16 ≤ B m r := by
  have h1 := mul_nonneg (sub_nonneg.mpr hr.2) (show 0 ≤ 1+m^2 by positivity)
  have h2 := mul_nonneg (show 0 ≤ 1-m/2 by linarith) (sq_nonneg r)
  have h3 := mul_nonneg (sub_nonneg.mpr hr.2) (show 0 ≤ 1/34+r by linarith)
  unfold B
  nlinarith only [h1,h2,h3,sq_nonneg m]

theorem common_criterion (x y p q r e tau v : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hm : p+q ≤ 2) (hr : 0 ≤ r ∧ r ≤ 1/34)
    (hcriterion : (1+3*(p+q)^2)/16-(1+p+q)*e^2 ≥ 0)
    (hcover : tau ≤ (1-r)^2/4+p*x+q*y-(p+q)/2-(p+q)^2/4+e^2)
    (hpacking : (1-r)*(1-2*r)/3+p*x*(x-r)+q*y*(y-r) ≤ (1+p+q)*v) : tau ≤ v := by
  let c := (1-r)^2/4+p*x+q*y-(p+q)/2-(p+q)^2/4+e^2
  let n := (1-r)*(1-2*r)/3+p*x*(x-r)+q*y*(y-r)
  have hid : n-(1+p+q)*c = B (p+q) r-(1+p+q)*e^2+
      p*(x-(1+p+q+r)/2)^2+q*(y-(1+p+q+r)/2)^2 := by dsimp [n,c,B]; ring
  have hB := common_margin (p+q) r ⟨add_nonneg hp hq,hm⟩ hr
  have h1 := mul_nonneg hp (sq_nonneg (x-(1+p+q+r)/2))
  have h2 := mul_nonneg hq (sq_nonneg (y-(1+p+q+r)/2))
  have hN : (1+p+q)*c ≤ n := by nlinarith only [hid,hB,hcriterion,h1,h2]
  have hpos : 0 < 1+p+q := by linarith
  have hle : c ≤ v := by
    by_contra h
    have hP := mul_pos hpos (sub_pos.mpr (lt_of_not_ge h))
    change n ≤ (1+p+q)*v at hpacking
    nlinarith only [hN,hpacking,hP]
  exact hcover.trans hle

#print axioms common_margin
#print axioms common_criterion
#check common_criterion
end TuzaNormalizedScalar


/-! A sound, data-driven finite certificate interface. -/
namespace TuzaFiniteCertificate
open Finset TuzaCompression TuzaGraphCompression TuzaIndependentAllocation TuzaMatchingClasses
  TuzaCoverCompression TuzaFiniteInterfaces TuzaShadowCovers TuzaRegionCuts TuzaFractionalOrders
variable {V : Type*} [DecidableEq V] [Fintype V]

structure Cut where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq, Repr

def feasible (k s t u : ℕ) (w : Cut) : Prop :=
  w.a ≤ s-u ∧ w.b ≤ t-u ∧ w.c ≤ u ∧ w.d ≤ k-(s+t-u)
instance (k s t u : ℕ) (w : Cut) : Decidable (feasible k s t u w) := inferInstanceAs
  (Decidable (w.a ≤ s-u ∧ w.b ≤ t-u ∧ w.c ≤ u ∧ w.d ≤ k-(s+t-u)))

def shadowUpper (k s t u : ℕ) (w : Cut) : ℕ :=
  shadowCost k (w.a+w.b+w.c+w.d) (w.a+w.c) (s-(w.a+w.c))
    (w.b+w.c) (t-(w.b+w.c)) w.c (u-w.c)

def cutUpper (k s t p q : ℕ) (w : Cut) : ℕ :=
  (w.a+w.b+w.c+w.d).choose 2+(k-(w.a+w.b+w.c+w.d)).choose 2+
    p*min (w.a+w.c) (s-(w.a+w.c))+q*min (w.b+w.c) (t-(w.b+w.c))

inductive Witness where
  | separable
  | shadow : Cut → Witness
  | cut : Cut → Witness
  deriving Repr

def validWitness (k s t u p q : ℕ) : Witness → Bool
  | .separable => decide (separableUpper k s t p q ≤ 2*packingLower k s t u p q)
  | .shadow w => decide (feasible k s t u w ∧ shadowUpper k s t u w ≤ 2*packingLower k s t u p q)
  | .cut w => decide (feasible k s t u w ∧ cutUpper k s t p q w ≤ 2*packingLower k s t u p q)

theorem outside_card_nat (S T : Finset V) :
    (outside S T).card = Fintype.card V-(S.card+T.card-(S ∩ T).card) := by
  have h1 := card_union_add_card_inter S T
  have h2 := card_sdiff_add_card_eq_card (subset_univ (S ∪ T))
  change (outside S T).card+(S ∪ T).card = (univ : Finset V).card at h2
  simp only [card_univ] at h2
  omega

theorem feasible_sets (S T : Finset V) (w : Cut)
    (h : feasible (Fintype.card V) S.card T.card (S ∩ T).card w) :
    w.a ≤ (S \ T).card ∧ w.b ≤ (T \ S).card ∧ w.c ≤ (S ∩ T).card ∧
      w.d ≤ (outside S T).card := by
  unfold feasible at h
  simpa only [card_sdiff,inter_comm T S,outside_card_nat] using h

theorem witness_sound (S T : Finset V) (hs : 2 ≤ S.card) (ht : 2 ≤ T.card)
    (hst : S.card ≤ T.card) (p q : ℕ) (hp : p ≤ colorCount S.card) (hq : q ≤ colorCount T.card)
    (w : Witness) (h : validWitness (Fintype.card V) S.card T.card (S ∩ T).card p q w = true) :
    coverNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) ≤
      2*packingNumber (twoAttached (⊤ : SimpleGraph V) S T (Fin p) (Fin q)) := by
  have hpack := Nat.mul_le_mul_left 2 (packingLower_sound S T hs ht hst p q hp hq)
  cases w with
  | separable =>
    have he := of_decide_eq_true h
    exact (separableUpper_sound S T p q).trans (he.trans hpack)
  | shadow w =>
    have he : feasible (Fintype.card V) S.card T.card (S ∩ T).card w ∧
        shadowUpper (Fintype.card V) S.card T.card (S ∩ T).card w ≤
          2*packingLower (Fintype.card V) S.card T.card (S ∩ T).card p q := of_decide_eq_true h
    obtain ⟨ha,hb,hc,hd⟩ := feasible_sets S T w he.1
    exact (integer_region_shadow S T p q w.a w.b w.c w.d ha hb hc hd).trans (he.2.trans hpack)
  | cut w =>
    have he : feasible (Fintype.card V) S.card T.card (S ∩ T).card w ∧
        cutUpper (Fintype.card V) S.card T.card p q w ≤
          2*packingLower (Fintype.card V) S.card T.card (S ∩ T).card p q := of_decide_eq_true h
    obtain ⟨ha,hb,hc,hd⟩ := feasible_sets S T w he.1
    exact (integer_region_cut S T p q w.a w.b w.c w.d ha hb hc hd).trans (he.2.trans hpack)

#print axioms outside_card_nat
#print axioms feasible_sets
#print axioms witness_sound
#check witness_sound
end TuzaFiniteCertificate


/-! Closed binomial formulas for efficient kernel reduction of the certificate. -/
namespace TuzaFiniteFast
open TuzaCompression TuzaFiniteInterfaces TuzaFiniteCertificate TuzaBalancedRounding
  TuzaShadowCovers TuzaGraphReductions

def c2 (n : ℕ) : ℕ := n*(n-1)/2
def c3 (n : ℕ) : ℕ := n*(n-1)*(n-2)/6

theorem c2_eq (n : ℕ) : c2 n = n.choose 2 := (Nat.choose_two_right n).symm

theorem c3_eq (n : ℕ) : c3 n = n.choose 3 := by
  by_cases hn : 2 ≤ n
  · have hc := choose_three_real n
    have hp : ((n*(n-1)*(n-2) : ℕ) : ℝ) = (n : ℝ)*((n : ℝ)-1)*((n : ℝ)-2) := by
      simp only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_sub hn,Nat.cast_one,Nat.cast_ofNat]
    have hR : (6 : ℝ)*(n.choose 3 : ℝ) = ((n*(n-1)*(n-2) : ℕ) : ℝ) := by rw [hp]; linarith only [hc]
    have hN : 6*n.choose 3 = n*(n-1)*(n-2) := by exact_mod_cast hR
    unfold c3
    rw [← hN]
    omega
  · have h : n = 0 ∨ n = 1 := by omega
    rcases h with rfl | rfl <;> decide

def core (k : ℕ) : ℕ := c2 k-k^2/4

def packing (k s t u p q : ℕ) : ℕ :=
  let i := ceilDiv (colorCount t*p*c2 s+colorCount s*q*c2 t-p*q*c2 u) (colorCount s*colorCount t)
  let j := ceilDiv (p*c2 s+q*c2 t-(p+q-colorCount t)*c2 u) (colorCount t)
  let ell := max i j
  let avg := fun r z => ceilDiv (c3 k+r*c2 s+z*c2 t) (k+r+z)
  max (ceilDiv (c3 k) k) (max ell (max (ceilDiv (core k+2*ell) 3)
    (max (avg p q) (max (avg p 0) (avg 0 q)))))

def separable (k s t p q : ℕ) : ℕ := (8*core k+p*penalty8 k s+q*penalty8 k t)/8

def shadow (k s t u : ℕ) (w : Cut) : ℕ :=
  let a := w.a+w.b+w.c+w.d
  c2 k-(a*(k-a)-((w.a+w.c)*(s-(w.a+w.c))+
    (w.b+w.c)*(t-(w.b+w.c))-w.c*(u-w.c)))

def cut (k s t p q : ℕ) (w : Cut) : ℕ :=
  let a := w.a+w.b+w.c+w.d
  c2 a+c2 (k-a)+p*min (w.a+w.c) (s-(w.a+w.c))+q*min (w.b+w.c) (t-(w.b+w.c))

def check (k s t u p q : ℕ) : Witness → Bool
  | .separable => decide (separable k s t p q ≤ 2*packing k s t u p q)
  | .shadow w => decide (feasible k s t u w ∧ shadow k s t u w ≤ 2*packing k s t u p q)
  | .cut w => decide (feasible k s t u w ∧ cut k s t p q w ≤ 2*packing k s t u p q)

theorem packing_eq (k s t u p q : ℕ) : packing k s t u p q = packingLower k s t u p q := by
  simp only [packing,core,c2_eq,c3_eq,packingLower,averageLower,outsideLower,outsideI,outsideC,coreBudget]

theorem check_eq (k s t u p q : ℕ) (w : Witness) :
    check k s t u p q w = validWitness k s t u p q w := by
  cases w <;> simp only [check,validWitness,packing_eq,separable,separableUpper,
    shadow,shadowUpper,shadowCost,cut,cutUpper,core,coreBudget,c2_eq]
    <;> exact congrArg (@decide _) (Subsingleton.elim _ _)

/-- These are actual region cuts; optimality is not an assumption. -/
def shadowFirst (k s t u : ℕ) : Cut := ⟨0,0,0,min (k-(s+t-u)) (k/2)⟩
def shadowSecond (k s t u : ℕ) : Cut := ⟨s-u,0,0,min (k-(s+t-u)) (k/2-(s-u))⟩

#print axioms c3_eq
#print axioms packing_eq
#print axioms check_eq
#check check_eq
end TuzaFiniteFast



namespace TuzaFiniteEnumeration
open TuzaFiniteCertificate TuzaFiniteFast TuzaCompression

def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n+1, f => f n && allBelow n f

theorem allBelow_sound (n : ℕ) (f : ℕ → Bool) (h : allBelow n f = true)
    (i : ℕ) (hi : i < n) : f i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [allBelow,Bool.and_eq_true] at h
    by_cases hin : i = n
    · simpa only [hin] using h.1
    · exact ih h.2 (by omega)

def allRange (lo hi : ℕ) (f : ℕ → Bool) : Bool :=
  allBelow (hi+1-lo) (fun j => f (lo+j))

theorem allRange_sound (lo hi : ℕ) (f : ℕ → Bool) (h : allRange lo hi f = true)
    (i : ℕ) (hl : lo ≤ i) (hh : i ≤ hi) : f i = true := by
  have he := allBelow_sound (hi+1-lo) (fun j => f (lo+j)) h (i-lo) (by omega)
  have hx : lo+(i-lo) = i := by omega
  simpa only [hx] using he

def shadowCandidates (k s t u : ℕ) : List Cut :=
  let sh := fun a b c => Cut.mk a b c (min (k-(s+t-u)) (k/2-(a+b+c)))
  [sh 0 0 0,sh (s-u) 0 0,sh 0 (t-u) 0,sh 0 0 u,
   sh (s-u) (t-u) 0,sh (s-u) 0 u,sh 0 (t-u) u,sh (s-u) (t-u) u]

def chooseShadow (k s t u p q : ℕ) (fallback : Cut) : List Cut → Witness
  | [] => .cut fallback
  | w::ws => if check k s t u p q (.shadow w) then .shadow w
      else chooseShadow k s t u p q fallback ws

def choose (fallback : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Cut) (k s t u p q : ℕ) : Witness :=
  if check k s t u p q .separable then .separable
  else chooseShadow k s t u p q (fallback k s t u p q) (shadowCandidates k s t u)

def coreCheck (fallback : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Cut) (k : ℕ) : Bool :=
  let f := fun s t u p q => check k s t u p q (choose fallback k s t u p q)
  allRange 2 k (fun s => allRange 0 (colorCount s) (fun p => f s s s p 0)) &&
  allRange 2 k (fun s => allRange s k (fun t => allRange (s+t-k) s (fun u =>
    allRange 1 (colorCount s) (fun p => allRange 1 (colorCount t) (fun q => f s t u p q)))))

theorem two_type_checked (fallback : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Cut)
    (k : ℕ) (h : coreCheck fallback k = true)
    (s t u p q : ℕ) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ k)
    (hu : s+t-k ≤ u ∧ u ≤ s) (hp : 1 ≤ p ∧ p ≤ colorCount s)
    (hq : 1 ≤ q ∧ q ≤ colorCount t) :
    validWitness k s t u p q (choose fallback k s t u p q) = true := by
  simp only [coreCheck,Bool.and_eq_true] at h
  have h1 := allRange_sound 2 k _ h.2 s hs (hst.trans ht)
  have h2 := allRange_sound s k _ h1 t hst ht
  have h3 := allRange_sound (s+t-k) s _ h2 u hu.1 hu.2
  have h4 := allRange_sound 1 (colorCount s) _ h3 p hp.1 hp.2
  have h5 := allRange_sound 1 (colorCount t) _ h4 q hq.1 hq.2
  rw [check_eq] at h5
  exact h5

theorem one_type_checked (fallback : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Cut)
    (k : ℕ) (h : coreCheck fallback k = true)
    (s p : ℕ) (hs : 2 ≤ s) (ht : s ≤ k) (hp : p ≤ colorCount s) :
    validWitness k s s s p 0 (choose fallback k s s s p 0) = true := by
  simp only [coreCheck,Bool.and_eq_true] at h
  have h1 := allRange_sound 2 k _ h.1 s hs ht
  have h2 := allRange_sound 0 (colorCount s) _ h1 p (Nat.zero_le _) hp
  rw [check_eq] at h2
  exact h2

#print axioms allRange_sound
#print axioms two_type_checked
#print axioms one_type_checked
#check two_type_checked
end TuzaFiniteEnumeration



/-! Positive scaling identities for the normalized certificate. -/
namespace TuzaHomogeneity
open TuzaSeparableCover TuzaCutFormulas

theorem scale_max {k : ℝ} (hk : 0 ≤ k) (a b : ℝ) :
    max (k*a) (k*b) = k*max a b := by
  by_cases h : a ≤ b
  · rw [max_eq_right h,max_eq_right (mul_le_mul_of_nonneg_left h hk)]
  · rw [max_eq_left (le_of_not_ge h),max_eq_left (mul_le_mul_of_nonneg_left (le_of_not_ge h) hk)]

theorem scale_min {k : ℝ} (hk : 0 ≤ k) (a b : ℝ) :
    min (k*a) (k*b) = k*min a b := by
  by_cases h : a ≤ b
  · rw [min_eq_left h,min_eq_left (mul_le_mul_of_nonneg_left h hk)]
  · rw [min_eq_right (le_of_not_ge h),min_eq_right (mul_le_mul_of_nonneg_left (le_of_not_ge h) hk)]

theorem scale_pos {k : ℝ} (hk : 0 ≤ k) (a : ℝ) : max 0 (k*a) = k*max 0 a := by
  simpa only [mul_zero] using scale_max hk 0 a

theorem penalty_scale (k d : ℝ) (hk : 0 ≤ k) : penalty k (k*d) = k*penalty 1 d := by
  unfold penalty
  rw [show k*d/2-k/8 = k*(d/2-1/8) by ring,
    show k*d-k/2 = k*(d-1/2) by ring,scale_max hk,scale_pos hk]

theorem costOne_scale (k x y w p q : ℝ) (hk : 0 ≤ k) :
    costOne k (k*x) (k*y) (k*w) (k*p) (k*q) = k^2*costOne 1 x y w p q := by
  unfold costOne
  rw [show k/2 = k*(1/2) by ring]
  simp only [← mul_sub,scale_min hk,scale_pos hk]
  ring

theorem costTwo_scale (k x y w p q : ℝ) (hk : 0 ≤ k) :
    costTwo k (k*x) (k*y) (k*w) (k*p) (k*q) = k^2*costTwo 1 x y w p q := by
  unfold costTwo
  rw [show k/2 = k*(1/2) by ring]
  simp only [← mul_sub,scale_min hk]
  ring

theorem costThree_scale (k x y w p q : ℝ) (hk : 0 ≤ k) :
    costThree k (k*x) (k*y) (k*w) (k*p) (k*q) = k^2*costThree 1 x y w p q := by
  unfold costThree
  rw [show k/2 = k*(1/2) by ring]
  simp only [← mul_sub,scale_pos hk,scale_max hk]
  ring

theorem costFour_scale (k x y w p q : ℝ) (hk : 0 ≤ k) :
    costFour k (k*x) (k*y) (k*w) (k*p) (k*q) = k^2*costFour 1 x y w p q := by
  unfold costFour
  rw [show k/2 = k*(1/2) by ring]
  simp only [← mul_sub,← mul_add,scale_pos hk]
  ring

#print axioms penalty_scale
#print axioms costOne_scale
#print axioms costTwo_scale
#print axioms costThree_scale
#print axioms costFour_scale
#check costFour_scale
end TuzaHomogeneity


/-! Check small disjoint parameter blocks, then assemble complete ranges. -/
namespace TuzaFiniteChunks
open TuzaFiniteCertificate TuzaFiniteFast TuzaFiniteEnumeration TuzaCompression

theorem allBelow_complete (n : ℕ) (f : ℕ → Bool) (h : ∀ i, i < n → f i = true) :
    allBelow n f = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allBelow,Bool.and_eq_true]
    exact ⟨h n (by omega),ih (fun i hi => h i (by omega))⟩

theorem allRange_complete (lo hi : ℕ) (f : ℕ → Bool)
    (h : ∀ i, lo ≤ i → i ≤ hi → f i = true) : allRange lo hi f = true := by
  apply allBelow_complete
  intro i hi'
  exact h (lo+i) (by omega) (by omega)

theorem allRange_merge (lo mid hi : ℕ) (f : ℕ → Bool)
    (hleft : allRange lo mid f = true) (hright : allRange (mid+1) hi f = true) :
    allRange lo hi f = true := by
  apply allRange_complete
  intro i hlo hhi
  by_cases hmid : i ≤ mid
  · exact allRange_sound lo mid f hleft i hlo hmid
  · exact allRange_sound (mid+1) hi f hright i (by omega) hhi

def pairCheck (fallback : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Cut) (k s t : ℕ) : Bool :=
  allRange (s+t-k) s (fun u => allRange 1 (colorCount s) (fun p =>
    allRange 1 (colorCount t) (fun q => check k s t u p q (choose fallback k s t u p q))))

def oneCheck (fallback : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Cut) (k : ℕ) : Bool :=
  allRange 2 k (fun s => allRange 0 (colorCount s) (fun p =>
    check k s s s p 0 (choose fallback k s s s p 0)))

theorem assemble_core (fallback : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Cut) (k : ℕ)
    (hone : oneCheck fallback k = true)
    (hrows : ∀ s, 2 ≤ s → s ≤ k → allRange s k (pairCheck fallback k s) = true) :
    coreCheck fallback k = true := by
  simp only [coreCheck,Bool.and_eq_true]
  refine ⟨hone,?_⟩
  exact allRange_complete 2 k _ hrows

#print axioms allRange_complete
#print axioms allRange_merge
#print axioms assemble_core
#check assemble_core
end TuzaFiniteChunks
