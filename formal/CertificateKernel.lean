import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Exact rational interval arithmetic, with soundness in the real numbers.
Certificate evaluation may compute rational endpoints; all soundness proofs
and all certificate equalities must be checked by the Lean kernel.
OpenAI Codex (GPT-6 Astra).
-/
namespace TuzaInterval

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

def Contains (a : Interval) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)

def point (q : ℚ) : Interval := ⟨q,q⟩
def add (a b : Interval) : Interval := ⟨a.lo+b.lo,a.hi+b.hi⟩
def neg (a : Interval) : Interval := ⟨-a.hi,-a.lo⟩
def mul (a b : Interval) : Interval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
def inv (a : Interval) : Interval := ⟨1/a.hi,1/a.lo⟩
def imax (a b : Interval) : Interval := ⟨max a.lo b.lo,max a.hi b.hi⟩
def imin (a b : Interval) : Interval := ⟨min a.lo b.lo,min a.hi b.hi⟩
def square (a : Interval) : Interval :=
  ⟨if a.lo ≤ 0 ∧ 0 ≤ a.hi then 0 else min (a.lo*a.lo) (a.hi*a.hi),
    max (a.lo*a.lo) (a.hi*a.hi)⟩

theorem point_sound (q : ℚ) : Contains (point q) (q : ℝ) := ⟨le_rfl,le_rfl⟩

theorem add_sound {a b : Interval} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (add a b) (x+y) := by
  unfold Contains add at *
  simp only [Rat.cast_add]
  exact ⟨add_le_add hx.1 hy.1,add_le_add hx.2 hy.2⟩

theorem neg_sound {a : Interval} {x : ℝ} (hx : Contains a x) : Contains (neg a) (-x) := by
  unfold Contains neg at *
  simp only [Rat.cast_neg]
  exact ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩

/-- An affine function on a real interval lies between its endpoint bounds. -/
theorem linear_bounds (l u a b x z : ℝ) (hx : a ≤ x ∧ x ≤ b)
    (ha : l ≤ a*z ∧ a*z ≤ u) (hb : l ≤ b*z ∧ b*z ≤ u) :
    l ≤ x*z ∧ x*z ≤ u := by
  by_cases hz : 0 ≤ z
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_right hx.1 hz),
      (mul_le_mul_of_nonneg_right hx.2 hz).trans hb.2⟩
  · have hz' : z ≤ 0 := le_of_not_ge hz
    exact ⟨hb.1.trans (mul_le_mul_of_nonpos_right hx.2 hz'),
      (mul_le_mul_of_nonpos_right hx.1 hz').trans ha.2⟩

set_option maxHeartbeats 800000 in
theorem mul_sound {a b : Interval} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (mul a b) (x*y) := by
  let l : ℝ := (mul a b).lo
  let u : ℝ := (mul a b).hi
  have hcorner (r s : ℚ) (hr : r = a.lo ∨ r = a.hi) (hs : s = b.lo ∨ s = b.hi) :
      l ≤ (r : ℝ)*(s : ℝ) ∧ (r : ℝ)*(s : ℝ) ≤ u := by
    have hh : (mul a b).lo ≤ r*s ∧ r*s ≤ (mul a b).hi := by
      rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
      · exact ⟨(min_le_left _ _).trans (min_le_left _ _),
          (le_max_left _ _).trans (le_max_left _ _)⟩
      · exact ⟨(min_le_left _ _).trans (min_le_right _ _),
          (le_max_right _ _).trans (le_max_left _ _)⟩
      · exact ⟨(min_le_right _ _).trans (min_le_left _ _),
          (le_max_left _ _).trans (le_max_right _ _)⟩
      · exact ⟨(min_le_right _ _).trans (min_le_right _ _),
          (le_max_right _ _).trans (le_max_right _ _)⟩
    change ((mul a b).lo : ℝ) ≤ (r : ℝ)*(s : ℝ) ∧ (r : ℝ)*(s : ℝ) ≤ ((mul a b).hi : ℝ)
    exact_mod_cast hh
  have h0 := linear_bounds l u a.lo a.hi x b.lo hx
    (hcorner _ _ (Or.inl rfl) (Or.inl rfl)) (hcorner _ _ (Or.inr rfl) (Or.inl rfl))
  have h1 := linear_bounds l u a.lo a.hi x b.hi hx
    (hcorner _ _ (Or.inl rfl) (Or.inr rfl)) (hcorner _ _ (Or.inr rfl) (Or.inr rfl))
  have h := linear_bounds l u b.lo b.hi y x hy (by simpa [mul_comm] using h0)
    (by simpa [mul_comm] using h1)
  change l ≤ x*y ∧ x*y ≤ u
  simpa only [mul_comm] using h

theorem inv_sound {a : Interval} {x : ℝ} (hx : Contains a x) (ha : 0 < a.lo) :
    Contains (inv a) (1/x) := by
  have hlo : (0 : ℝ) < a.lo := by exact_mod_cast ha
  have hpos : 0 < x := hlo.trans_le hx.1
  unfold Contains inv
  simp only [Rat.cast_div,Rat.cast_one]
  exact ⟨one_div_le_one_div_of_le hpos hx.2,one_div_le_one_div_of_le hlo hx.1⟩

theorem imax_sound {a b : Interval} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (imax a b) (max x y) := by
  have hcast (r s : ℚ) : ((max r s : ℚ) : ℝ) = max (r : ℝ) (s : ℝ) := by
    by_cases h : r ≤ s
    · rw [max_eq_right h,max_eq_right (by exact_mod_cast h)]
    · rw [max_eq_left (le_of_not_ge h),max_eq_left (by exact_mod_cast le_of_not_ge h)]
  unfold Contains imax
  rw [hcast,hcast]
  exact ⟨max_le_max hx.1 hy.1,max_le_max hx.2 hy.2⟩

theorem imin_sound {a b : Interval} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (imin a b) (min x y) := by
  have hcast (r s : ℚ) : ((min r s : ℚ) : ℝ) = min (r : ℝ) (s : ℝ) := by
    by_cases h : r ≤ s
    · rw [min_eq_left h,min_eq_left (by exact_mod_cast h)]
    · rw [min_eq_right (le_of_not_ge h),min_eq_right (by exact_mod_cast le_of_not_ge h)]
  unfold Contains imin
  rw [hcast,hcast]
  exact ⟨min_le_min hx.1 hy.1,min_le_min hx.2 hy.2⟩

theorem square_sound {a : Interval} {x : ℝ} (hx : Contains a x) :
    Contains (square a) (x*x) := by
  have h0 : ((min (a.lo*a.lo) (a.hi*a.hi) : ℚ) : ℝ) ≤ (a.lo : ℝ)*(a.lo : ℝ) := by exact_mod_cast min_le_left (a.lo*a.lo) (a.hi*a.hi)
  have h1 : ((min (a.lo*a.lo) (a.hi*a.hi) : ℚ) : ℝ) ≤ (a.hi : ℝ)*(a.hi : ℝ) := by exact_mod_cast min_le_right (a.lo*a.lo) (a.hi*a.hi)
  have h2 : (a.lo : ℝ)*(a.lo : ℝ) ≤ ((max (a.lo*a.lo) (a.hi*a.hi) : ℚ) : ℝ) := by exact_mod_cast le_max_left (a.lo*a.lo) (a.hi*a.hi)
  have h3 : (a.hi : ℝ)*(a.hi : ℝ) ≤ ((max (a.lo*a.lo) (a.hi*a.hi) : ℚ) : ℝ) := by exact_mod_cast le_max_right (a.lo*a.lo) (a.hi*a.hi)
  unfold Contains square
  constructor
  · split_ifs with hz
    · simp only [Rat.cast_zero]
      exact mul_self_nonneg x
    · have hn : ¬((a.lo : ℝ) ≤ 0 ∧ 0 ≤ (a.hi : ℝ)) := by exact_mod_cast hz
      rcases hx with ⟨hlo,hhi⟩
      by_cases hp : 0 ≤ x
      · have hl : 0 ≤ (a.lo : ℝ) := by by_contra h; apply hn; constructor <;> linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ x+(a.lo : ℝ) by linarith)]
      · have hu : (a.hi : ℝ) ≤ 0 := by by_contra h; apply hn; constructor <;> linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ -x-(a.hi : ℝ) by linarith)]
  · rcases hx with ⟨hlo,hhi⟩
    by_cases hp : 0 ≤ x
    · nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ x+(a.hi : ℝ) by linarith)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ -x-(a.lo : ℝ) by linarith)]

inductive Expr (n : ℕ) where
  | const : ℚ → Expr n
  | var : Fin n → Expr n
  | add : Expr n → Expr n → Expr n
  | neg : Expr n → Expr n
  | mul : Expr n → Expr n → Expr n
  | inv : Expr n → Expr n
  | max : Expr n → Expr n → Expr n
  | min : Expr n → Expr n → Expr n
  | square : Expr n → Expr n
  deriving Repr

def eval {n : ℕ} (box : Fin n → Interval) : Expr n → Interval
  | .const q => point q
  | .var i => box i
  | .add a b => add (eval box a) (eval box b)
  | .neg a => neg (eval box a)
  | .mul a b => mul (eval box a) (eval box b)
  | .inv a => inv (eval box a)
  | .max a b => imax (eval box a) (eval box b)
  | .min a b => imin (eval box a) (eval box b)
  | .square a => square (eval box a)

def valid {n : ℕ} (box : Fin n → Interval) : Expr n → Bool
  | .const _ | .var _ => true
  | .add a b | .mul a b | .max a b | .min a b => valid box a && valid box b
  | .neg a | .square a => valid box a
  | .inv a => valid box a && decide (0 < (eval box a).lo)

noncomputable def value {n : ℕ} (x : Fin n → ℝ) : Expr n → ℝ
  | .const q => q
  | .var i => x i
  | .add a b => value x a+value x b
  | .neg a => -value x a
  | .mul a b => value x a*value x b
  | .inv a => 1/value x a
  | .max a b => max (value x a) (value x b)
  | .min a b => min (value x a) (value x b)
  | .square a => value x a*value x a

theorem eval_sound {n : ℕ} (box : Fin n → Interval) (x : Fin n → ℝ)
    (hx : ∀ i, Contains (box i) (x i)) (e : Expr n) (he : valid box e = true) :
    Contains (eval box e) (value x e) := by
  induction e with
  | const q => exact point_sound q
  | var i => exact hx i
  | add a b ha hb =>
    simp only [valid,Bool.and_eq_true] at he
    exact add_sound (ha he.1) (hb he.2)
  | neg a ha => exact neg_sound (ha he)
  | mul a b ha hb =>
    simp only [valid,Bool.and_eq_true] at he
    exact mul_sound (ha he.1) (hb he.2)
  | inv a ha =>
    simp only [valid,Bool.and_eq_true,decide_eq_true_eq] at he
    exact inv_sound (ha he.1) he.2
  | max a b ha hb =>
    simp only [valid,Bool.and_eq_true] at he
    exact imax_sound (ha he.1) (hb he.2)
  | min a b ha hb =>
    simp only [valid,Bool.and_eq_true] at he
    exact imin_sound (ha he.1) (hb he.2)
  | square a ha => exact square_sound (ha he)

#print axioms mul_sound
#print axioms inv_sound
#print axioms square_sound
#print axioms eval_sound
#check eval_sound
end TuzaInterval

/-! Domain-preserving box contraction and subdivision. -/
namespace TuzaCertificate
open TuzaInterval
abbrev Box := Fin 6 → Interval
abbrev Point := Fin 6 → ℝ

def Mem (b : Box) (v : Point) : Prop := ∀ i, Contains (b i) (v i)

structure Domain (v : Point) : Prop where
  xy : v 0 ≤ v 1
  wx : v 2 ≤ v 0
  union : v 0+v 1-1 ≤ v 2
  px : v 3 ≤ v 0
  qy : v 4 ≤ v 1
  rp : v 5 ≤ v 3
  rq : v 5 ≤ v 4
  mass : 1+5*v 5 ≤ 3*(v 3+v 4)

def raise (b : Box) (i : Fin 6) (l : ℚ) : Box :=
  Function.update b i ⟨max (b i).lo l,(b i).hi⟩
def lower (b : Box) (i : Fin 6) (u : ℚ) : Box :=
  Function.update b i ⟨(b i).lo,min (b i).hi u⟩

theorem raise_sound (b : Box) (v : Point) (h : Mem b v) (i : Fin 6) (l : ℚ)
    (hl : (l : ℝ) ≤ v i) : Mem (raise b i l) v := by
  intro j
  by_cases hj : j = i
  · subst j
    simp only [raise,Function.update_self,Contains]
    have hc : ((max (b i).lo l : ℚ) : ℝ) = max ((b i).lo : ℝ) (l : ℝ) := by
      by_cases hh : (b i).lo ≤ l
      · rw [max_eq_right hh,max_eq_right (by exact_mod_cast hh)]
      · rw [max_eq_left (le_of_not_ge hh),max_eq_left (by exact_mod_cast le_of_not_ge hh)]
    rw [hc]
    exact ⟨max_le (h i).1 hl,(h i).2⟩
  · simpa only [raise,Function.update_of_ne hj] using h j

theorem lower_sound (b : Box) (v : Point) (h : Mem b v) (i : Fin 6) (u : ℚ)
    (hu : v i ≤ (u : ℝ)) : Mem (lower b i u) v := by
  intro j
  by_cases hj : j = i
  · subst j
    simp only [lower,Function.update_self,Contains]
    have hc : ((min (b i).hi u : ℚ) : ℝ) = min ((b i).hi : ℝ) (u : ℝ) := by
      by_cases hh : (b i).hi ≤ u
      · rw [min_eq_left hh,min_eq_left (by exact_mod_cast hh)]
      · rw [min_eq_right (le_of_not_ge hh),min_eq_right (by exact_mod_cast le_of_not_ge hh)]
    rw [hc]
    exact ⟨(h i).1,le_min (h i).2 hu⟩
  · simpa only [lower,Function.update_of_ne hj] using h j

def step0 (b : Box) : Box := lower b 0 ((b 1).hi)

theorem step0_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step0 b) v := by
  apply lower_sound b v h 0
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step1 (b : Box) : Box := raise b 1 ((b 0).lo)

theorem step1_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step1 b) v := by
  apply raise_sound b v h 1
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step2 (b : Box) : Box := lower b 2 ((b 0).hi)

theorem step2_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step2 b) v := by
  apply lower_sound b v h 2
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step3 (b : Box) : Box := raise b 0 ((b 2).lo)

theorem step3_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step3 b) v := by
  apply raise_sound b v h 0
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step4 (b : Box) : Box := raise b 2 ((b 0).lo+(b 1).lo-1)

theorem step4_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step4 b) v := by
  apply raise_sound b v h 2
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step5 (b : Box) : Box := lower b 0 (1+(b 2).hi-(b 1).lo)

theorem step5_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step5 b) v := by
  apply lower_sound b v h 0
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step6 (b : Box) : Box := lower b 1 (1+(b 2).hi-(b 0).lo)

theorem step6_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step6 b) v := by
  apply lower_sound b v h 1
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step7 (b : Box) : Box := lower b 3 ((b 0).hi)

theorem step7_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step7 b) v := by
  apply lower_sound b v h 3
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step8 (b : Box) : Box := raise b 0 ((b 3).lo)

theorem step8_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step8 b) v := by
  apply raise_sound b v h 0
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step9 (b : Box) : Box := raise b 3 ((b 5).lo)

theorem step9_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step9 b) v := by
  apply raise_sound b v h 3
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step10 (b : Box) : Box := lower b 5 ((b 3).hi)

theorem step10_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step10 b) v := by
  apply lower_sound b v h 5
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step11 (b : Box) : Box := lower b 4 ((b 1).hi)

theorem step11_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step11 b) v := by
  apply lower_sound b v h 4
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step12 (b : Box) : Box := raise b 1 ((b 4).lo)

theorem step12_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step12 b) v := by
  apply raise_sound b v h 1
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step13 (b : Box) : Box := raise b 4 ((b 5).lo)

theorem step13_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step13 b) v := by
  apply raise_sound b v h 4
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step14 (b : Box) : Box := lower b 5 ((b 4).hi)

theorem step14_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step14 b) v := by
  apply lower_sound b v h 5
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step15 (b : Box) : Box := raise b 3 ((1+5*(b 5).lo-3*(b 4).hi)/3)

theorem step15_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step15 b) v := by
  apply raise_sound b v h 3
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step16 (b : Box) : Box := raise b 4 ((1+5*(b 5).lo-3*(b 3).hi)/3)

theorem step16_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step16 b) v := by
  apply raise_sound b v h 4
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step17 (b : Box) : Box := lower b 5 ((3*(b 3).hi+3*(b 4).hi-1)/5)

theorem step17_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (step17 b) v := by
  apply lower_sound b v h 5
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := hd
  simp only [Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def contract (b : Box) : Box :=
  let b := step0 b
  let b := step1 b
  let b := step2 b
  let b := step3 b
  let b := step4 b
  let b := step5 b
  let b := step6 b
  let b := step7 b
  let b := step8 b
  let b := step9 b
  let b := step10 b
  let b := step11 b
  let b := step12 b
  let b := step13 b
  let b := step14 b
  let b := step15 b
  let b := step16 b
  let b := step17 b
  b

theorem contract_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (contract b) v := by
  unfold contract
  apply step17_sound _ v hd
  apply step16_sound _ v hd
  apply step15_sound _ v hd
  apply step14_sound _ v hd
  apply step13_sound _ v hd
  apply step12_sound _ v hd
  apply step11_sound _ v hd
  apply step10_sound _ v hd
  apply step9_sound _ v hd
  apply step8_sound _ v hd
  apply step7_sound _ v hd
  apply step6_sound _ v hd
  apply step5_sound _ v hd
  apply step4_sound _ v hd
  apply step3_sound _ v hd
  apply step2_sound _ v hd
  apply step1_sound _ v hd
  apply step0_sound _ v hd
  exact h

def contract3 (b : Box) : Box := contract (contract (contract b))

theorem contract3_sound (b : Box) (v : Point) (hd : Domain v) (h : Mem b v) :
    Mem (contract3 b) v := contract_sound _ _ hd (contract_sound _ _ hd (contract_sound _ _ hd h))

def isEmpty (b : Box) : Bool := decide (∃ i, (b i).hi < (b i).lo)

theorem empty_sound (b : Box) (h : isEmpty b = true) : ∀ v, ¬Mem b v := by
  intro v hv
  obtain ⟨i,hi⟩ := of_decide_eq_true h
  have hiR : ((b i).hi : ℝ) < (b i).lo := by exact_mod_cast hi
  exact (not_lt_of_ge ((hv i).1.trans (hv i).2)) hiR

inductive Tree where
  | leaf : Tree
  | split : Fin 6 → ℚ → Tree → Tree → Tree
  deriving Repr

def check (accept : Box → Bool) (b : Box) : Tree → Bool
  | .leaf => let c := contract3 b; isEmpty c || accept c
  | .split i m left right => let c := contract3 b
    isEmpty c || (check accept (lower c i m) left && check accept (raise c i m) right)

theorem check_sound (accept : Box → Bool) (P : Point → Prop)
    (ha : ∀ b, accept b = true → ∀ v, Domain v → Mem b v → P v)
    (t : Tree) (b : Box) (hc : check accept b t = true) :
    ∀ v, Domain v → Mem b v → P v := by
  induction t generalizing b with
  | leaf =>
    intro v hd hv
    have hm := contract3_sound b v hd hv
    simp only [check,Bool.or_eq_true] at hc
    rcases hc with he | he
    · exact False.elim (empty_sound _ he v hm)
    · exact ha _ he v hd hm
  | split i m l r hl hr =>
    intro v hd hv
    have hm := contract3_sound b v hd hv
    simp only [check,Bool.or_eq_true,Bool.and_eq_true] at hc
    rcases hc with he | he
    · exact False.elim (empty_sound _ he v hm)
    · by_cases hvm : v i ≤ (m : ℝ)
      · exact hl _ he.1 v hd (lower_sound _ v hm i m hvm)
      · exact hr _ he.2 v hd (raise_sound _ v hm i m (le_of_not_ge hvm))

#print axioms contract_sound
#print axioms contract3_sound
#print axioms empty_sound
#print axioms check_sound
#check check_sound
end TuzaCertificate

/-! Explicit expressions evaluated by the continuous certificate. -/
namespace TuzaCertificateExpressions
open TuzaInterval TuzaCertificate

instance {n : ℕ} : Add (Expr n) := ⟨Expr.add⟩
instance {n : ℕ} : Neg (Expr n) := ⟨Expr.neg⟩
instance {n : ℕ} : Sub (Expr n) := ⟨fun a b => .add a (.neg b)⟩
instance {n : ℕ} : Mul (Expr n) := ⟨Expr.mul⟩
instance {n : ℕ} : Div (Expr n) := ⟨fun a b => .mul a (.inv b)⟩
instance {n k : ℕ} : OfNat (Expr n) k := ⟨.const k⟩

def x : Expr 6 := .var 0
def y : Expr 6 := .var 1
def w : Expr 6 := .var 2
def p : Expr 6 := .var 3
def q : Expr 6 := .var 4
def rho : Expr 6 := .var 5
def m : Expr 6 := p+q
def rat (a b : ℚ) : Expr 6 := .const (a/b)
def half : Expr 6 := rat 1 2
def quarter : Expr 6 := rat 1 4
def pos (a : Expr 6) : Expr 6 := .max 0 a
def sq (a : Expr 6) : Expr 6 := .square a
def f (a : Expr 6) : Expr 6 := .max (pos (a/2-rat 1 8)) (a-half)
def excess : Expr 6 := pos ((1+m)/2-w)

def common : Expr 6 := (1+3*sq m)/16-(1+m)*sq excess

def coverCosts : List (Expr 6) :=
  [p*f x+q*f y,
   quarter-sq rho/4-y*(1-y)+(.min (w*pos (x-w)) (sq x/4)),
   p*(x-half)+q*(y-half)-sq m/4+sq excess,
   p*pos (x-half)+q*pos (y-(.min w half)-pos (half-x)),
   q*(y-half)+p*(x-(.min w half)),
   p*pos (x-half)+q*(.max (y-half) (w-pos (x-half))),
   q*(y-half)+p*pos (w-y+half)]

def i0 : Expr 6 := p*x+q*y-p*q*sq w/(x*y)
def i1 : Expr 6 := m-p*q*w/(x*y)
def j0 : Expr 6 := (p*sq x+q*sq y-pos (m-y)*sq w)/y
def j1 : Expr 6 := (p*x+q*y-pos (m-y)*w)/y

def outsideGap (base loss : Expr 6) : Expr 6 :=
  base-quarter+rho*(half-loss)-sq rho/4

def completionGap (base loss : Expr 6) : Expr 6 :=
  -(rat 1 12)+2*base/3+rho*(rat 1 6-2*loss/3)-sq rho/4

def averageGap (r t : Expr 6) : Expr 6 :=
  (rat 1 12+r*(sq x-quarter)+t*(sq y-quarter)+
    rho*(-half+r*(half-x)+t*(half-y))+
    sq rho*(rat 5 12-(r+t)/4))/(1+r+t)

def packingGaps : List (Expr 6) :=
  [rat 1 12-rho/2+5*sq rho/12,
   outsideGap i0 i1,completionGap i0 i1,
   outsideGap j0 j1,completionGap j0 j1,
   averageGap p q,averageGap p 0,averageGap 0 q]

def nonnegative (b : Box) (e : Expr 6) : Bool :=
  valid b e && decide (0 ≤ (eval b e).lo)

def compare (b : Box) (a c : Expr 6) : Bool :=
  valid b a && (valid b c && decide ((eval b a).hi ≤ (eval b c).lo))

def anyCompare (b : Box) (a : Expr 6) : List (Expr 6) → Bool
  | [] => false
  | c::cs => compare b a c || anyCompare b a cs

def anyCover (b : Box) (gaps : List (Expr 6)) : List (Expr 6) → Bool
  | [] => false
  | a::as => anyCompare b a gaps || anyCover b gaps as

def accept (b : Box) : Bool := nonnegative b common || anyCover b packingGaps coverCosts

noncomputable def Conclusion (v : Point) : Prop :=
  0 ≤ value v common ∨ ∃ a ∈ coverCosts, ∃ c ∈ packingGaps, value v a ≤ value v c

theorem nonnegative_sound (b : Box) (v : Point) (hv : Mem b v) (e : Expr 6)
    (h : nonnegative b e = true) : 0 ≤ value v e := by
  simp only [nonnegative,Bool.and_eq_true,decide_eq_true_eq] at h
  have he := eval_sound b v hv e h.1
  have hl : (0 : ℝ) ≤ (eval b e).lo := by exact_mod_cast h.2
  exact hl.trans he.1

theorem compare_sound (b : Box) (v : Point) (hv : Mem b v) (a c : Expr 6)
    (h : compare b a c = true) : value v a ≤ value v c := by
  simp only [compare,Bool.and_eq_true,decide_eq_true_eq] at h
  have ha := eval_sound b v hv a h.1
  have hc := eval_sound b v hv c h.2.1
  have hm : ((eval b a).hi : ℝ) ≤ (eval b c).lo := by exact_mod_cast h.2.2
  exact ha.2.trans (hm.trans hc.1)

theorem anyCompare_sound (b : Box) (v : Point) (hv : Mem b v) (a : Expr 6)
    (cs : List (Expr 6)) (h : anyCompare b a cs = true) :
    ∃ c ∈ cs, value v a ≤ value v c := by
  induction cs with
  | nil => simp [anyCompare] at h
  | cons c cs ih =>
    simp only [anyCompare,Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨c,by simp,compare_sound b v hv a c h⟩
    · obtain ⟨d,hd,he⟩ := ih h
      exact ⟨d,by simp [hd],he⟩

theorem anyCover_sound (b : Box) (v : Point) (hv : Mem b v) (cs as : List (Expr 6))
    (h : anyCover b cs as = true) : ∃ a ∈ as, ∃ c ∈ cs, value v a ≤ value v c := by
  induction as with
  | nil => simp [anyCover] at h
  | cons a as ih =>
    simp only [anyCover,Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨a,by simp,anyCompare_sound b v hv a cs h⟩
    · obtain ⟨a',ha,hc⟩ := ih h
      exact ⟨a',by simp [ha],hc⟩

theorem accept_sound (b : Box) (h : accept b = true) (v : Point)
    (_hd : Domain v) (hv : Mem b v) : Conclusion v := by
  simp only [accept,Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (nonnegative_sound b v hv common h)
  · exact Or.inr (anyCover_sound b v hv packingGaps coverCosts h)

theorem certificate_sound (t : Tree) (b : Box) (h : check accept b t = true) :
    ∀ v, Domain v → Mem b v → Conclusion v :=
  check_sound accept Conclusion accept_sound t b h

#print axioms nonnegative_sound
#print axioms compare_sound
#print axioms anyCompare_sound
#print axioms anyCover_sound
#print axioms accept_sound
#print axioms certificate_sound
#check certificate_sound
end TuzaCertificateExpressions


/-! Untrusted hints and precomputed boxes speed up the same kernel checks. -/
namespace TuzaGuided
open TuzaInterval TuzaCertificate TuzaCertificateExpressions

inductive Hint where
  | common
  | pair (cover : Fin 7) (packing : Fin 8)
  deriving Repr

def select (b : Box) : Hint → Bool
  | .common => nonnegative b common
  | .pair i j => compare b (coverCosts.get i) (packingGaps.get j)

theorem select_sound (b : Box) (v : Point) (hv : Mem b v) (hint : Hint)
    (hh : select b hint = true) : Conclusion v := by
  cases hint with
  | common => exact Or.inl (nonnegative_sound b v hv common hh)
  | pair i j =>
    exact Or.inr ⟨coverCosts.get i,List.get_mem _ _,packingGaps.get j,List.get_mem _ _,
      compare_sound b v hv _ _ hh⟩

/-- `encloses a b` checks that every point in b also belongs to a. -/
def encloses (a b : Box) : Bool := decide (∀ i, (a i).lo ≤ (b i).lo ∧ (b i).hi ≤ (a i).hi)

theorem encloses_sound (a b : Box) (h : encloses a b = true) (v : Point) (hv : Mem b v) : Mem a v := by
  have hh : ∀ i, (a i).lo ≤ (b i).lo ∧ (b i).hi ≤ (a i).hi := of_decide_eq_true h
  intro i
  have hlo : ((a i).lo : ℝ) ≤ (b i).lo := by exact_mod_cast (hh i).1
  have hhi : ((b i).hi : ℝ) ≤ (a i).hi := by exact_mod_cast (hh i).2
  exact ⟨hlo.trans (hv i).1,(hv i).2.trans hhi⟩

inductive Tree where
  | leaf (box : Box) (hint : Hint)
  | split (box : Box) (axis : Fin 6) (pivot : ℚ) (left right : Tree)

def check (b : Box) : Tree → Bool
  | .leaf c hint => encloses c (contract3 b) && select c hint
  | .split c i m l r => encloses c (contract3 b) &&
      (check (lower c i m) l && check (raise c i m) r)

theorem check_sound (tree : Tree) (b : Box) (hc : check b tree = true) :
    ∀ v, Domain v → Mem b v → Conclusion v := by
  induction tree generalizing b with
  | leaf c hint =>
    simp only [check,Bool.and_eq_true] at hc
    intro v hd hv
    exact select_sound c v (encloses_sound c _ hc.1 v (contract3_sound b v hd hv)) hint hc.2
  | split c i m l r ihl ihr =>
    simp only [check,Bool.and_eq_true] at hc
    intro v hd hv
    have hcMem := encloses_sound c _ hc.1 v (contract3_sound b v hd hv)
    by_cases h : v i ≤ (m : ℝ)
    · exact ihl (lower c i m) hc.2.1 v hd (lower_sound c v hcMem i m h)
    · exact ihr (raise c i m) hc.2.2 v hd (raise_sound c v hcMem i m (le_of_not_ge h))

#print axioms select_sound
#print axioms encloses_sound
#print axioms check_sound
#check check_sound
end TuzaGuided

/-! Fixed-point interval evaluation with proved outward rounding. -/
namespace TuzaDyadic
open TuzaInterval

def scale : ℤ := 1208925819614629174706176
noncomputable abbrev R : ℝ := scale

theorem scale_pos : (0 : ℤ) < scale := by decide
theorem R_pos : 0 < R := by
  change (0 : ℝ) < (scale : ℝ)
  exact_mod_cast scale_pos

theorem cancel_left {a b : ℝ} (h : R*a ≤ R*b) : a ≤ b := by
  by_contra hn
  have hp := mul_pos R_pos (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hp,h]

theorem cancel_right {a b : ℝ} (h : a*R ≤ b*R) : a ≤ b := by
  apply cancel_left
  simpa only [mul_comm] using h

structure Interval where
  lo : ℤ
  hi : ℤ
  deriving Repr, DecidableEq

def Contains (a : Interval) (x : ℝ) : Prop := (a.lo : ℝ) ≤ R*x ∧ R*x ≤ (a.hi : ℝ)
def ceilDiv (a b : ℤ) : ℤ := -((-a)/b)

theorem floor_mul (a b : ℤ) (hb : b ≠ 0) : ((a/b : ℤ) : ℝ)*(b : ℝ) ≤ (a : ℝ) := by
  exact_mod_cast Int.ediv_mul_le a hb

theorem ceil_mul (a b : ℤ) (hb : b ≠ 0) : (a : ℝ) ≤ (ceilDiv a b : ℝ)*(b : ℝ) := by
  have h := floor_mul (-a) b hb
  simp only [ceilDiv,Int.cast_neg] at *
  nlinarith only [h]

theorem floor_bound (a b : ℤ) (hb : 0 < b) : ((a/b : ℤ) : ℝ) ≤ (a : ℝ)/(b : ℝ) := by
  exact (le_div_iff₀ (by exact_mod_cast hb)).mpr (floor_mul a b hb.ne')

theorem ceil_bound (a b : ℤ) (hb : 0 < b) : (a : ℝ)/(b : ℝ) ≤ (ceilDiv a b : ℝ) := by
  exact (div_le_iff₀ (by exact_mod_cast hb)).mpr (ceil_mul a b hb.ne')

def point (q : ℚ) : Interval := ⟨q.num*scale/q.den,ceilDiv (q.num*scale) q.den⟩
def add (a b : Interval) : Interval := ⟨a.lo+b.lo,a.hi+b.hi⟩
def neg (a : Interval) : Interval := ⟨-a.hi,-a.lo⟩
def round (lo hi : ℤ) : Interval := ⟨lo/scale,ceilDiv hi scale⟩
def prodLo (a b : Interval) : ℤ := min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))
def prodHi (a b : Interval) : ℤ := max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))
def mul (a b : Interval) : Interval := round (prodLo a b) (prodHi a b)
def inv (a : Interval) : Interval := ⟨scale*scale/a.hi,ceilDiv (scale*scale) a.lo⟩
def imax (a b : Interval) : Interval := ⟨max a.lo b.lo,max a.hi b.hi⟩
def imin (a b : Interval) : Interval := ⟨min a.lo b.lo,min a.hi b.hi⟩
def sqLo (a : Interval) : ℤ := if a.lo ≤ 0 ∧ 0 ≤ a.hi then 0 else min (a.lo*a.lo) (a.hi*a.hi)
def sqHi (a : Interval) : ℤ := max (a.lo*a.lo) (a.hi*a.hi)
def square (a : Interval) : Interval := round (sqLo a) (sqHi a)

theorem point_sound (q : ℚ) : Contains (point q) (q : ℝ) := by
  have hd : (0 : ℤ) < (q.den : ℤ) := by exact_mod_cast q.pos
  have hl := floor_bound (q.num*scale) q.den hd
  have hh := ceil_bound (q.num*scale) q.den hd
  have he : ((q.num*scale : ℤ) : ℝ)/(q.den : ℝ) = R*(q : ℝ) := by
    rw [Rat.cast_def]
    push_cast
    ring
  simp only [Int.cast_natCast] at hl hh
  rw [he] at hl hh
  exact ⟨hl,hh⟩

theorem add_sound {a b : Interval} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (add a b) (x+y) := by
  simp only [Contains,add,Int.cast_add] at *
  constructor <;> linarith

theorem neg_sound {a : Interval} {x : ℝ} (hx : Contains a x) : Contains (neg a) (-x) := by
  simp only [Contains,neg,Int.cast_neg] at *
  constructor <;> linarith

theorem round_sound (lo hi : ℤ) (x : ℝ) (h : (lo : ℝ) ≤ R^2*x ∧ R^2*x ≤ (hi : ℝ)) :
    Contains (round lo hi) x := by
  constructor
  · apply cancel_right
    calc ((lo/scale : ℤ) : ℝ)*R ≤ (lo : ℝ) := floor_mul lo scale scale_pos.ne'
      _ ≤ R^2*x := h.1
      _ = (R*x)*R := by ring
  · apply cancel_right
    calc (R*x)*R = R^2*x := by ring
      _ ≤ (hi : ℝ) := h.2
      _ ≤ (ceilDiv hi scale : ℝ)*R := ceil_mul hi scale scale_pos.ne'

set_option maxHeartbeats 800000 in
theorem mul_sound {a b : Interval} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (mul a b) (x*y) := by
  let l : ℝ := prodLo a b
  let u : ℝ := prodHi a b
  have corners (r s : ℤ) (hr : r = a.lo ∨ r = a.hi) (hs : s = b.lo ∨ s = b.hi) :
      l ≤ (r : ℝ)*(s : ℝ) ∧ (r : ℝ)*(s : ℝ) ≤ u := by
    have hh : prodLo a b ≤ r*s ∧ r*s ≤ prodHi a b := by
      rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
      · exact ⟨(min_le_left _ _).trans (min_le_left _ _),(le_max_left _ _).trans (le_max_left _ _)⟩
      · exact ⟨(min_le_left _ _).trans (min_le_right _ _),(le_max_right _ _).trans (le_max_left _ _)⟩
      · exact ⟨(min_le_right _ _).trans (min_le_left _ _),(le_max_left _ _).trans (le_max_right _ _)⟩
      · exact ⟨(min_le_right _ _).trans (min_le_right _ _),(le_max_right _ _).trans (le_max_right _ _)⟩
    dsimp only [l,u]
    exact_mod_cast hh
  have h0 := TuzaInterval.linear_bounds l u a.lo a.hi (R*x) b.lo hx
    (corners _ _ (Or.inl rfl) (Or.inl rfl)) (corners _ _ (Or.inr rfl) (Or.inl rfl))
  have h1 := TuzaInterval.linear_bounds l u a.lo a.hi (R*x) b.hi hx
    (corners _ _ (Or.inl rfl) (Or.inr rfl)) (corners _ _ (Or.inr rfl) (Or.inr rfl))
  have h := TuzaInterval.linear_bounds l u b.lo b.hi (R*y) (R*x) hy
    (by simpa only [mul_comm] using h0) (by simpa only [mul_comm] using h1)
  apply round_sound
  dsimp only [l,u] at h
  constructor <;> nlinarith only [h]

theorem inv_sound {a : Interval} {x : ℝ} (hx : Contains a x) (ha : 0 < a.lo) :
    Contains (inv a) (1/x) := by
  have hlo : (0 : ℝ) < a.lo := by exact_mod_cast ha
  have hRx : 0 < R*x := hlo.trans_le hx.1
  have hx0 : 0 < x := (mul_pos_iff_of_pos_left R_pos).mp hRx
  have hhi : (0 : ℝ) < a.hi := hRx.trans_le hx.2
  have hi : 0 < a.hi := by exact_mod_cast hhi
  have he : R^2*(1/(R*x)) = R*(1/x) := by field_simp [R_pos.ne',hx0.ne'] <;> ring
  have l := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hRx hx.2) (sq_nonneg R)
  have u := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hlo hx.1) (sq_nonneg R)
  rw [he] at l u
  have fl := floor_bound (scale*scale) a.hi hi
  have fu := ceil_bound (scale*scale) a.lo ha
  simp only [Int.cast_mul] at fl fu
  change Contains (inv a) (1/x)
  constructor <;> dsimp only [inv]
  · calc ((scale*scale/a.hi : ℤ) : ℝ) ≤ R^2*(1/(a.hi : ℝ)) := by simpa only [R,pow_two,one_div,div_eq_mul_inv,one_mul] using fl
      _ ≤ R*(1/x) := l
  · calc R*(1/x) ≤ R^2*(1/(a.lo : ℝ)) := u
      _ ≤ (ceilDiv (scale*scale) a.lo : ℝ) := by simpa only [R,pow_two,one_div,div_eq_mul_inv,one_mul] using fu

theorem cast_max (a b : ℤ) : ((max a b : ℤ) : ℝ) = max (a : ℝ) (b : ℝ) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h,max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left (le_of_not_ge h),max_eq_left (by exact_mod_cast le_of_not_ge h)]

theorem cast_min (a b : ℤ) : ((min a b : ℤ) : ℝ) = min (a : ℝ) (b : ℝ) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h,min_eq_left (by exact_mod_cast h)]
  · rw [min_eq_right (le_of_not_ge h),min_eq_right (by exact_mod_cast le_of_not_ge h)]

theorem imax_sound {a b : Interval} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (imax a b) (max x y) := by
  have he : R*max x y = max (R*x) (R*y) := by
    by_cases h : x ≤ y
    · rw [max_eq_right h,max_eq_right (mul_le_mul_of_nonneg_left h R_pos.le)]
    · rw [max_eq_left (le_of_not_ge h),max_eq_left (mul_le_mul_of_nonneg_left (le_of_not_ge h) R_pos.le)]
  simp only [Contains,imax,cast_max,he]
  exact ⟨max_le_max hx.1 hy.1,max_le_max hx.2 hy.2⟩

theorem imin_sound {a b : Interval} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (imin a b) (min x y) := by
  have he : R*min x y = min (R*x) (R*y) := by
    by_cases h : x ≤ y
    · rw [min_eq_left h,min_eq_left (mul_le_mul_of_nonneg_left h R_pos.le)]
    · rw [min_eq_right (le_of_not_ge h),min_eq_right (mul_le_mul_of_nonneg_left (le_of_not_ge h) R_pos.le)]
  simp only [Contains,imin,cast_min,he]
  exact ⟨min_le_min hx.1 hy.1,min_le_min hx.2 hy.2⟩

theorem square_sound {a : Interval} {x : ℝ} (hx : Contains a x) : Contains (square a) (x*x) := by
  apply round_sound
  have h0 : ((min (a.lo*a.lo) (a.hi*a.hi) : ℤ) : ℝ) ≤ (a.lo : ℝ)*(a.lo : ℝ) := by exact_mod_cast min_le_left (a.lo*a.lo) (a.hi*a.hi)
  have h1 : ((min (a.lo*a.lo) (a.hi*a.hi) : ℤ) : ℝ) ≤ (a.hi : ℝ)*(a.hi : ℝ) := by exact_mod_cast min_le_right (a.lo*a.lo) (a.hi*a.hi)
  have h2 : (a.lo : ℝ)*(a.lo : ℝ) ≤ ((max (a.lo*a.lo) (a.hi*a.hi) : ℤ) : ℝ) := by exact_mod_cast le_max_left (a.lo*a.lo) (a.hi*a.hi)
  have h3 : (a.hi : ℝ)*(a.hi : ℝ) ≤ ((max (a.lo*a.lo) (a.hi*a.hi) : ℤ) : ℝ) := by exact_mod_cast le_max_right (a.lo*a.lo) (a.hi*a.hi)
  have hs : R^2*(x*x) = (R*x)*(R*x) := by ring
  rw [hs]
  constructor
  · unfold sqLo
    split_ifs with hz
    · simp only [Int.cast_zero]; exact mul_self_nonneg (R*x)
    · have hn : ¬((a.lo : ℝ) ≤ 0 ∧ 0 ≤ (a.hi : ℝ)) := by exact_mod_cast hz
      rcases hx with ⟨hlo,hhi⟩
      by_cases hp : 0 ≤ R*x
      · have hl : 0 ≤ (a.lo : ℝ) := by by_contra h; apply hn; constructor <;> linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ R*x+(a.lo : ℝ) by linarith)]
      · have hu : (a.hi : ℝ) ≤ 0 := by by_contra h; apply hn; constructor <;> linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ -R*x-(a.hi : ℝ) by linarith)]
  · unfold sqHi
    rcases hx with ⟨hlo,hhi⟩
    by_cases hp : 0 ≤ R*x
    · nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ R*x+(a.hi : ℝ) by linarith)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ -R*x-(a.lo : ℝ) by linarith)]

def eval {n : ℕ} (box : Fin n → Interval) : Expr n → Interval
  | .const q => point q
  | .var i => box i
  | .add a b => add (eval box a) (eval box b)
  | .neg a => neg (eval box a)
  | .mul a b => mul (eval box a) (eval box b)
  | .inv a => inv (eval box a)
  | .max a b => imax (eval box a) (eval box b)
  | .min a b => imin (eval box a) (eval box b)
  | .square a => square (eval box a)

def valid {n : ℕ} (box : Fin n → Interval) : Expr n → Bool
  | .const _ | .var _ => true
  | .add a b | .mul a b | .max a b | .min a b => valid box a && valid box b
  | .neg a | .square a => valid box a
  | .inv a => valid box a && decide (0 < (eval box a).lo)

theorem eval_sound {n : ℕ} (box : Fin n → Interval) (x : Fin n → ℝ)
    (hx : ∀ i, Contains (box i) (x i)) (e : Expr n) (he : valid box e = true) :
    Contains (eval box e) (TuzaInterval.value x e) := by
  induction e with
  | const q => exact point_sound q
  | var i => exact hx i
  | add a b ha hb =>
    simp only [valid,Bool.and_eq_true] at he
    exact add_sound (ha he.1) (hb he.2)
  | neg a ha => exact neg_sound (ha he)
  | mul a b ha hb =>
    simp only [valid,Bool.and_eq_true] at he
    exact mul_sound (ha he.1) (hb he.2)
  | inv a ha =>
    simp only [valid,Bool.and_eq_true,decide_eq_true_eq] at he
    exact inv_sound (ha he.1) he.2
  | max a b ha hb =>
    simp only [valid,Bool.and_eq_true] at he
    exact imax_sound (ha he.1) (hb he.2)
  | min a b ha hb =>
    simp only [valid,Bool.and_eq_true] at he
    exact imin_sound (ha he.1) (hb he.2)
  | square a ha => exact square_sound (ha he)

#print axioms floor_bound
#print axioms ceil_bound
#print axioms point_sound
#print axioms mul_sound
#print axioms inv_sound
#print axioms square_sound
#print axioms eval_sound
#check eval_sound
end TuzaDyadic

namespace TuzaDyadicCertificate
open TuzaDyadic TuzaCertificateExpressions
abbrev Box := Fin 6 → TuzaDyadic.Interval
abbrev Point := Fin 6 → ℝ
def Mem (b : Box) (v : Point) : Prop := ∀ i, TuzaDyadic.Contains (b i) (v i)

def raise (b : Box) (i : Fin 6) (l : ℤ) : Box := Function.update b i ⟨max (b i).lo l,(b i).hi⟩
def lower (b : Box) (i : Fin 6) (u : ℤ) : Box := Function.update b i ⟨(b i).lo,min (b i).hi u⟩

theorem raise_sound (b : Box) (v : Point) (h : Mem b v) (i : Fin 6) (l : ℤ)
    (hl : (l : ℝ) ≤ R*v i) : Mem (raise b i l) v := by
  intro j
  by_cases hj : j = i
  · subst j
    simp only [raise,Function.update_self,TuzaDyadic.Contains,cast_max]
    exact ⟨max_le (h i).1 hl,(h i).2⟩
  · simpa only [raise,Function.update_of_ne hj] using h j

theorem lower_sound (b : Box) (v : Point) (h : Mem b v) (i : Fin 6) (u : ℤ)
    (hu : R*v i ≤ (u : ℝ)) : Mem (lower b i u) v := by
  intro j
  by_cases hj : j = i
  · subst j
    simp only [lower,Function.update_self,TuzaDyadic.Contains,cast_min]
    exact ⟨(h i).1,le_min (h i).2 hu⟩
  · simpa only [lower,Function.update_of_ne hj] using h j

theorem scaled_domain (v : Point) (h : TuzaCertificate.Domain v) :
    R*v 0 ≤ R*v 1 ∧ R*v 2 ≤ R*v 0 ∧ R*v 0+R*v 1-R ≤ R*v 2 ∧
    R*v 3 ≤ R*v 0 ∧ R*v 4 ≤ R*v 1 ∧ R*v 5 ≤ R*v 3 ∧ R*v 5 ≤ R*v 4 ∧
    R+5*(R*v 5) ≤ 3*(R*v 3+R*v 4) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := h
  refine ⟨mul_le_mul_of_nonneg_left h0 R_pos.le,mul_le_mul_of_nonneg_left h1 R_pos.le,?_,
    mul_le_mul_of_nonneg_left h3 R_pos.le,mul_le_mul_of_nonneg_left h4 R_pos.le,
    mul_le_mul_of_nonneg_left h5 R_pos.le,mul_le_mul_of_nonneg_left h6 R_pos.le,?_⟩
  · nlinarith only [mul_le_mul_of_nonneg_left h2 R_pos.le]
  · nlinarith only [mul_le_mul_of_nonneg_left h7 R_pos.le]

def step0 (b : Box) : Box := lower b 0 ((b 1).hi)

theorem step0_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step0 b) v := by
  apply lower_sound b v h 0
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step1 (b : Box) : Box := raise b 1 ((b 0).lo)

theorem step1_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step1 b) v := by
  apply raise_sound b v h 1
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step2 (b : Box) : Box := lower b 2 ((b 0).hi)

theorem step2_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step2 b) v := by
  apply lower_sound b v h 2
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step3 (b : Box) : Box := raise b 0 ((b 2).lo)

theorem step3_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step3 b) v := by
  apply raise_sound b v h 0
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step4 (b : Box) : Box := raise b 2 ((b 0).lo+(b 1).lo-scale)

theorem step4_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step4 b) v := by
  apply raise_sound b v h 2
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step5 (b : Box) : Box := lower b 0 (scale+(b 2).hi-(b 1).lo)

theorem step5_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step5 b) v := by
  apply lower_sound b v h 0
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step6 (b : Box) : Box := lower b 1 (scale+(b 2).hi-(b 0).lo)

theorem step6_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step6 b) v := by
  apply lower_sound b v h 1
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step7 (b : Box) : Box := lower b 3 ((b 0).hi)

theorem step7_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step7 b) v := by
  apply lower_sound b v h 3
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step8 (b : Box) : Box := raise b 0 ((b 3).lo)

theorem step8_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step8 b) v := by
  apply raise_sound b v h 0
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step9 (b : Box) : Box := raise b 3 ((b 5).lo)

theorem step9_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step9 b) v := by
  apply raise_sound b v h 3
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step10 (b : Box) : Box := lower b 5 ((b 3).hi)

theorem step10_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step10 b) v := by
  apply lower_sound b v h 5
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step11 (b : Box) : Box := lower b 4 ((b 1).hi)

theorem step11_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step11 b) v := by
  apply lower_sound b v h 4
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step12 (b : Box) : Box := raise b 1 ((b 4).lo)

theorem step12_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step12 b) v := by
  apply raise_sound b v h 1
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step13 (b : Box) : Box := raise b 4 ((b 5).lo)

theorem step13_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step13 b) v := by
  apply raise_sound b v h 4
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step14 (b : Box) : Box := lower b 5 ((b 4).hi)

theorem step14_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step14 b) v := by
  apply lower_sound b v h 5
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  push_cast
  linarith

def step15 (b : Box) : Box := raise b 3 ((scale+5*(b 5).lo-3*(b 4).hi)/3)

theorem step15_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step15 b) v := by
  apply raise_sound b v h 3
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  have hf := floor_mul (scale+5*(b 5).lo-3*(b 4).hi) 3 (by decide)
  push_cast at hf ⊢
  linarith

def step16 (b : Box) : Box := raise b 4 ((scale+5*(b 5).lo-3*(b 3).hi)/3)

theorem step16_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step16 b) v := by
  apply raise_sound b v h 4
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  have hf := floor_mul (scale+5*(b 5).lo-3*(b 3).hi) 3 (by decide)
  push_cast at hf ⊢
  linarith

def step17 (b : Box) : Box := lower b 5 (ceilDiv (3*(b 3).hi+3*(b 4).hi-scale) 5)

theorem step17_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) :
    Mem (step17 b) v := by
  apply lower_sound b v h 5
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := scaled_domain v hd
  simp only [TuzaDyadic.Contains] at h0 h1 h2 h3 h4 h5
  have hf := ceil_mul (3*(b 3).hi+3*(b 4).hi-scale) 5 (by decide)
  push_cast at hf ⊢
  linarith

def contract (b : Box) : Box := step17 (step16 (step15 (step14 (step13 (step12 (step11 (step10 (step9 (step8 (step7 (step6 (step5 (step4 (step3 (step2 (step1 (step0 (b))))))))))))))))))

theorem contract_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) : Mem (contract b) v := by
  unfold contract
  apply step17_sound _ v hd
  apply step16_sound _ v hd
  apply step15_sound _ v hd
  apply step14_sound _ v hd
  apply step13_sound _ v hd
  apply step12_sound _ v hd
  apply step11_sound _ v hd
  apply step10_sound _ v hd
  apply step9_sound _ v hd
  apply step8_sound _ v hd
  apply step7_sound _ v hd
  apply step6_sound _ v hd
  apply step5_sound _ v hd
  apply step4_sound _ v hd
  apply step3_sound _ v hd
  apply step2_sound _ v hd
  apply step1_sound _ v hd
  apply step0_sound _ v hd
  exact h

def contract3 (b : Box) : Box := contract (contract (contract b))

theorem contract3_sound (b : Box) (v : Point) (hd : TuzaCertificate.Domain v) (h : Mem b v) : Mem (contract3 b) v :=
  contract_sound _ v hd (contract_sound _ v hd (contract_sound b v hd h))

#print axioms scaled_domain
#print axioms contract_sound
#print axioms contract3_sound
#check contract3_sound
end TuzaDyadicCertificate

namespace TuzaDyadicCertificate
open TuzaDyadic TuzaCertificateExpressions

def nonnegative (b : Box) (e : TuzaInterval.Expr 6) : Bool :=
  valid b e && decide (0 ≤ (eval b e).lo)

def compare (b : Box) (a c : TuzaInterval.Expr 6) : Bool :=
  valid b a && (valid b c && decide ((eval b a).hi ≤ (eval b c).lo))

def select (b : Box) : TuzaGuided.Hint → Bool
  | .common => nonnegative b common
  | .pair i j => compare b (coverCosts.get i) (packingGaps.get j)

theorem nonnegative_sound (b : Box) (v : Point) (hv : Mem b v) (e : TuzaInterval.Expr 6)
    (h : nonnegative b e = true) : 0 ≤ TuzaInterval.value v e := by
  simp only [nonnegative,Bool.and_eq_true,decide_eq_true_eq] at h
  have he := eval_sound b v hv e h.1
  have hl : (0 : ℝ) ≤ (eval b e).lo := by exact_mod_cast h.2
  have hh := hl.trans he.1
  apply cancel_left
  simpa only [mul_zero] using hh

theorem compare_sound (b : Box) (v : Point) (hv : Mem b v) (a c : TuzaInterval.Expr 6)
    (h : compare b a c = true) : TuzaInterval.value v a ≤ TuzaInterval.value v c := by
  simp only [compare,Bool.and_eq_true,decide_eq_true_eq] at h
  have ha := eval_sound b v hv a h.1
  have hc := eval_sound b v hv c h.2.1
  have hm : ((eval b a).hi : ℝ) ≤ (eval b c).lo := by exact_mod_cast h.2.2
  exact cancel_left (ha.2.trans (hm.trans hc.1))

theorem select_sound (b : Box) (v : Point) (hv : Mem b v) (hint : TuzaGuided.Hint)
    (hh : select b hint = true) : Conclusion v := by
  cases hint with
  | common => exact Or.inl (nonnegative_sound b v hv common hh)
  | pair i j => exact Or.inr ⟨coverCosts.get i,List.get_mem _ _,packingGaps.get j,List.get_mem _ _,
      compare_sound b v hv _ _ hh⟩

def encloses (a b : Box) : Bool := decide (∀ i, (a i).lo ≤ (b i).lo ∧ (b i).hi ≤ (a i).hi)

theorem encloses_sound (a b : Box) (h : encloses a b = true) (v : Point) (hv : Mem b v) : Mem a v := by
  have hh : ∀ i, (a i).lo ≤ (b i).lo ∧ (b i).hi ≤ (a i).hi := of_decide_eq_true h
  intro i
  have hlo : ((a i).lo : ℝ) ≤ (b i).lo := by exact_mod_cast (hh i).1
  have hhi : ((b i).hi : ℝ) ≤ (a i).hi := by exact_mod_cast (hh i).2
  exact ⟨hlo.trans (hv i).1,(hv i).2.trans hhi⟩

inductive Tree where
  | leaf (box : Box) (hint : TuzaGuided.Hint)
  | split (box : Box) (axis : Fin 6) (pivot : ℤ) (left right : Tree)

def check (b : Box) : Tree → Bool
  | .leaf c hint => encloses c (contract3 b) && select c hint
  | .split c i m l r => encloses c (contract3 b) && (check (lower c i m) l && check (raise c i m) r)

theorem check_sound (tree : Tree) (b : Box) (hc : check b tree = true) :
    ∀ v, TuzaCertificate.Domain v → Mem b v → Conclusion v := by
  induction tree generalizing b with
  | leaf c hint =>
    simp only [check,Bool.and_eq_true] at hc
    intro v hd hv
    exact select_sound c v (encloses_sound c _ hc.1 v (contract3_sound b v hd hv)) hint hc.2
  | split c i m l r ihl ihr =>
    simp only [check,Bool.and_eq_true] at hc
    intro v hd hv
    have hcMem := encloses_sound c _ hc.1 v (contract3_sound b v hd hv)
    by_cases h : R*v i ≤ (m : ℝ)
    · exact ihl (lower c i m) hc.2.1 v hd (lower_sound c v hcMem i m h)
    · exact ihr (raise c i m) hc.2.2 v hd (raise_sound c v hcMem i m (le_of_not_ge h))

theorem split_join (b c lb rb : Box) (i : Fin 6) (m : ℤ)
    (hc : encloses c (contract3 b) = true)
    (hl : encloses lb (lower c i m) = true)
    (hr : encloses rb (raise c i m) = true)
    (left : ∀ v, TuzaCertificate.Domain v → Mem lb v → Conclusion v)
    (right : ∀ v, TuzaCertificate.Domain v → Mem rb v → Conclusion v) :
    ∀ v, TuzaCertificate.Domain v → Mem b v → Conclusion v := by
  intro v hd hv
  have hcMem := encloses_sound c _ hc v (contract3_sound b v hd hv)
  by_cases h : R*v i ≤ (m : ℝ)
  · exact left v hd (encloses_sound lb _ hl v (lower_sound c v hcMem i m h))
  · exact right v hd (encloses_sound rb _ hr v (raise_sound c v hcMem i m (le_of_not_ge h)))

#print axioms nonnegative_sound
#print axioms compare_sound
#print axioms select_sound
#print axioms encloses_sound
#print axioms check_sound
#print axioms split_join
#check split_join
end TuzaDyadicCertificate

/-! Only the contraction steps recorded in an untrusted hint are evaluated.
Each permitted step has already been proved to preserve every domain point. -/
namespace TuzaTraceCertificate
open TuzaDyadic TuzaDyadicCertificate TuzaCertificateExpressions

def step (b : Box) (i : Fin 18) : Box := match i.val with
  | 0 => step0 b
  | 1 => step1 b
  | 2 => step2 b
  | 3 => step3 b
  | 4 => step4 b
  | 5 => step5 b
  | 6 => step6 b
  | 7 => step7 b
  | 8 => step8 b
  | 9 => step9 b
  | 10 => step10 b
  | 11 => step11 b
  | 12 => step12 b
  | 13 => step13 b
  | 14 => step14 b
  | 15 => step15 b
  | 16 => step16 b
  | _ => step17 b

theorem step_sound (i : Fin 18) (b : Box) (v : Point) (hd : TuzaCertificate.Domain v)
    (h : Mem b v) : Mem (step b i) v := by
  fin_cases i
  · exact step0_sound b v hd h
  · exact step1_sound b v hd h
  · exact step2_sound b v hd h
  · exact step3_sound b v hd h
  · exact step4_sound b v hd h
  · exact step5_sound b v hd h
  · exact step6_sound b v hd h
  · exact step7_sound b v hd h
  · exact step8_sound b v hd h
  · exact step9_sound b v hd h
  · exact step10_sound b v hd h
  · exact step11_sound b v hd h
  · exact step12_sound b v hd h
  · exact step13_sound b v hd h
  · exact step14_sound b v hd h
  · exact step15_sound b v hd h
  · exact step16_sound b v hd h
  · exact step17_sound b v hd h

def run (b : Box) : List (Fin 18) → Box
  | [] => b
  | i::is => run (step b i) is

theorem run_sound (trace : List (Fin 18)) (b : Box) (v : Point)
    (hd : TuzaCertificate.Domain v) (h : Mem b v) : Mem (run b trace) v := by
  induction trace generalizing b with
  | nil => exact h
  | cons i is ih => exact ih (step b i) (step_sound i b v hd h)

inductive Tree where
  | leaf (box : Box) (trace : List (Fin 18)) (hint : TuzaGuided.Hint)
  | split (box : Box) (trace : List (Fin 18)) (axis : Fin 6) (pivot : ℤ) (left right : Tree)

def check (b : Box) : Tree → Bool
  | .leaf c trace hint => encloses c (run b trace) && select c hint
  | .split c trace i m l r => encloses c (run b trace) && (check (lower c i m) l && check (raise c i m) r)

theorem check_sound (tree : Tree) (b : Box) (hc : check b tree = true) :
    ∀ v, TuzaCertificate.Domain v → Mem b v → Conclusion v := by
  induction tree generalizing b with
  | leaf c trace hint =>
    simp only [check,Bool.and_eq_true] at hc
    intro v hd hv
    exact select_sound c v (encloses_sound c _ hc.1 v (run_sound trace b v hd hv)) hint hc.2
  | split c trace i m l r ihl ihr =>
    simp only [check,Bool.and_eq_true] at hc
    intro v hd hv
    have hcMem := encloses_sound c _ hc.1 v (run_sound trace b v hd hv)
    by_cases h : R*v i ≤ (m : ℝ)
    · exact ihl (lower c i m) hc.2.1 v hd (lower_sound c v hcMem i m h)
    · exact ihr (raise c i m) hc.2.2 v hd (raise_sound c v hcMem i m (le_of_not_ge h))

theorem split_join (b c lb rb : Box) (trace : List (Fin 18)) (i : Fin 6) (m : ℤ)
    (hc : encloses c (run b trace) = true)
    (hl : encloses lb (lower c i m) = true)
    (hr : encloses rb (raise c i m) = true)
    (left : ∀ v, TuzaCertificate.Domain v → Mem lb v → Conclusion v)
    (right : ∀ v, TuzaCertificate.Domain v → Mem rb v → Conclusion v) :
    ∀ v, TuzaCertificate.Domain v → Mem b v → Conclusion v := by
  intro v hd hv
  have hcMem := encloses_sound c _ hc v (run_sound trace b v hd hv)
  by_cases h : R*v i ≤ (m : ℝ)
  · exact left v hd (encloses_sound lb _ hl v (lower_sound c v hcMem i m h))
  · exact right v hd (encloses_sound rb _ hr v (raise_sound c v hcMem i m (le_of_not_ge h)))

#print axioms step_sound
#print axioms run_sound
#print axioms check_sound
#print axioms split_join
end TuzaTraceCertificate
