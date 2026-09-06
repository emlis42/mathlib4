/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib

/-!
# The complex `LambertW` function

TODO: add doc, add local notation doc, add tag
-/

@[expose] public noncomputable section

namespace Complex

open Real Set Filter Topology

open scoped ComplexConjugate

variable {α : Type*} {k : ℤ} {z w : ℂ}

section LambertWRange

/-- TODO doc -/
def LambertW.slitPlane (k : ℤ) : Set ℂ :=
  if k = 0 then {z | -(rexp 1)⁻¹ < z.re ∨ z.im ≠ 0} else Complex.slitPlane

/-- TODO doc -/
def LambertW.branchCut (k : ℤ) : Set ℂ :=
  (slitPlane k)ᶜ

/-- TODO doc -/
def LambertW.boundaryAux (k : ℤ) : Set ℂ :=
  (fun t => ⟨-t * Real.cot t, t⟩) '' Ioo (k * π) ((k + 1) * π)

/-- TODO doc -/
def LambertW.upperBoundary (k : ℤ) : Set ℂ := match k with
  | Int.ofNat (_ + 1) => LambertW.boundaryAux (2 * k)
  | 0 => LambertW.boundaryAux 0 ∪ {-1}
  | -1 => LambertW.branchCut 0 ∪ LambertW.boundaryAux (-1)
  | Int.negSucc (_ + 1) => LambertW.boundaryAux (2 * k + 1)

/-- TODO doc -/
def LambertW.lowerBoundary (k : ℤ) : Set ℂ := match k with
  | Int.ofNat (_ + 2) => LambertW.boundaryAux (2 * k - 2)
  | 1 => LambertW.boundaryAux 0 ∪ {-1}
  | 0 => LambertW.boundaryAux (-1)
  | Int.negSucc _ => LambertW.boundaryAux (2 * k + 1)

/-- TODO doc -/
def LambertW.BelowBondary (k : ℤ) (w : ℂ) : Prop :=
  ∃ z ∈ upperBoundary k, w.re = z.re ∧ w.im ≤ z.im

/-- TODO doc -/
def LambertW.StrictBelowBondary (k : ℤ) (w : ℂ) : Prop :=
  ∃ z ∈ upperBoundary k, w.re = z.re ∧ w.im < z.im

/-- TODO doc -/
def LambertW.StrictAboveBoundary (k : ℤ) (w : ℂ) : Prop :=
  ∃ z ∈ upperBoundary k, w.re = z.re ∧ z.im < w.im

/-- TODO doc -/
def LambertW.domain (k : ℤ) : Set ℂ :=
  if k = 0 then univ else {0}ᶜ

/-- TODO doc -/
def LambertW.range (k : ℤ) : Set ℂ :=
  {w | LambertW.StrictAboveBoundary k w ∧ LambertW.BelowBondary k w} ∪ {w | w = 0 ∧ k = 0}

/-- TODO doc -/
def LambertW.openRange (k : ℤ) : Set ℂ :=
  {w | LambertW.StrictAboveBoundary k w ∧ LambertW.StrictBelowBondary k w}

theorem LambertW.belowBondary_of_strictBelowBondary :
    StrictBelowBondary k w -> BelowBondary k w := by
  grind [StrictBelowBondary, BelowBondary]

@[simp]
theorem LambertW.domain_zero : domain 0 = univ :=
  rfl

theorem LambertW.domain_of_ne_zero (hk : k ≠ 0) : domain k = {0}ᶜ :=
  ite_eq_right hk

theorem LambertW.mem_domain_of_ne_zero (hz : z ≠ 0) : z ∈ domain k :=
  em (k = 0) |>.elim (fun hk => hk ▸ trivial) (fun hk => domain_of_ne_zero hk ▸ hz)

theorem LambertW.image_mul_exp_range_zero : (fun w => w * cexp w) '' range 0 = univ := by
  refine eq_univ_iff_forall.mpr fun w => ?_
  simp
  sorry

theorem LambertW.image_mul_exp_range_of_ne_zero (hk : k ≠ 0) :
    (fun w => w * cexp w) '' range k = {0}ᶜ := by
  sorry

theorem LambertW.image_mul_exp_range :
    (fun w => w * cexp w) '' range k = domain k := by
  by_cases hk : k = 0
  · rw [hk, image_mul_exp_range_zero, domain_zero]
  · rw [image_mul_exp_range_of_ne_zero hk, domain_of_ne_zero hk]

theorem LambertW.mapsTo_mul_exp_range :
    MapsTo (fun w => w * cexp w) (range k) (domain k) := by
  simpa only [← image_mul_exp_range] using mapsTo_image _ _

theorem LambertW.mapsTo_mul_exp_range_zero :
    MapsTo (fun w => w * cexp w) (range 0) univ := by
  simpa only [← domain_zero] using mapsTo_mul_exp_range

theorem LambertW.mapsTo_mul_exp_range_of_ne_zero (hk : k ≠ 0) :
    MapsTo (fun w => w * cexp w) (range k) {0}ᶜ := by
  simpa only [← domain_of_ne_zero hk] using mapsTo_mul_exp_range

theorem LambertW.injOn_mul_exp_range :
    InjOn (fun w => w * cexp w) (range k) := by
  sorry

theorem LambertW.surjOn_mul_exp_range :
    SurjOn (fun w => w * cexp w) (range k) (domain k) := by
  simpa only [← image_mul_exp_range] using surjOn_image _ _

theorem LambertW.surjOn_mul_exp_range_zero :
    SurjOn (fun w => w * cexp w) (range 0) univ := by
  simpa only [← domain_zero] using surjOn_mul_exp_range

theorem LambertW.surjOn_mul_exp_range_of_ne_zero (hk : k ≠ 0) :
    SurjOn (fun w => w * cexp w) (range k) {0}ᶜ := by
  simpa only [← domain_of_ne_zero hk] using surjOn_mul_exp_range

theorem LambertW.bijOn_mul_exp_range_domain :
    BijOn (fun w => w * cexp w) (range k) (domain k) :=
  ⟨mapsTo_mul_exp_range, injOn_mul_exp_range, surjOn_mul_exp_range⟩

theorem LambertW.bijOn_mul_exp_range_domain_zero :
    BijOn (fun w => w * cexp w) (range 0) univ := by
  simpa only [← domain_zero] using bijOn_mul_exp_range_domain

theorem LambertW.bijOn_mul_exp_range_domain_of_ne_zero (hk : k ≠ 0) :
    BijOn (fun w => w * cexp w) (range k) {0}ᶜ := by
  simpa only [← domain_of_ne_zero hk] using bijOn_mul_exp_range_domain

theorem LambertW.iUnion_range : ⋃ k, range k = univ := by
  sorry

theorem LambertW.neg_one_mem_range_zero : -1 ∈ range 0 := by
  sorry

theorem LambertW.neg_one_mem_range_neg_one : -1 ∈ range (-1) := by
  sorry

theorem LambertW.neg_one_not_mem_range_of_ne : k ≠ 0 ∧ k ≠ (-1) -> -1 ∉ range k := by
  sorry

theorem LambertW.range_inter_eq_empty {i j : ℤ} (h1 : i ≠ j) (h2 : ({i, j} : Finset ℤ) ≠ {0, -1}) :
    range i ∩ range j = ∅ := by
  simp at h2
  sorry

theorem LambertW.existsUnique_mem_range_of_ne_neg_one (hw : w ≠ -1) :
    ∃! k, w ∈ range k := by
  sorry

theorem LambertW.zero_mem_range_iff : 0 ∈ range k ↔ k = 0 := by
  sorry

theorem LambertW.openRange_subset_range : openRange k ⊆ range k := by
  grind [belowBondary_of_strictBelowBondary, openRange, range]

theorem LambertW.slitPlane_subset_domain : slitPlane k ⊆ domain k := by
  unfold slitPlane domain
  split_ifs with hk <;> simp

end LambertWRange

section LambertW

open LambertW

/-- TODO doc -/
def lambertW (k : ℤ) : ℂ -> ℂ :=
  Function.invFunOn (fun w => w * cexp w) (LambertW.range k)

@[inherit_doc] scoped[ComplexLambertW] notation "W_ " => Complex.lambertW
recommended_spelling "lambertW" for "W_" in [lambertW, ComplexLambertW.«termW_»]

open scoped ComplexLambertW

/-- TODO doc -/
scoped[ComplexLambertW] notation "W₀" => W_ 0
recommended_spelling "lambertW_zero" for "W₀" in [ComplexLambertW.«termW₀»]

/-- TODO doc -/
scoped[ComplexLambertW] notation "W₋₁" => W_ (-1)
recommended_spelling "lambertW_neg_one" for "W₋₁" in [ComplexLambertW.«termW₋₁»]

theorem LambertW.apply_mem_range_of_mem_domain
    (hz : z ∈ domain k) : W_ k z ∈ range k := by
  refine Function.invFunOn_mem ?_
  rwa [← mem_image, bijOn_mul_exp_range_domain.image_eq]

theorem LambertW.apply_zero_mem_range : W₀ z ∈ range 0 :=
  LambertW.apply_mem_range_of_mem_domain trivial

theorem LambertW.apply_mul_exp_of_mem_range (hw : w ∈ range k) : W_ k (w * exp w) = w :=
  LambertW.bijOn_mul_exp_range_domain.invOn_invFunOn.left hw

theorem LambertW.apply_mul_exp_apply_of_mem_domain (hz : z ∈ domain k) :
    W_ k z * cexp (W_ k z) = z := by
  apply Function.invFunOn_eq (f := fun w => w * exp w)
  rwa [← mem_image, bijOn_mul_exp_range_domain.image_eq]

@[simp]
theorem lambertW_zero_mul_exp_lambertW_zero : W₀ z * cexp (W₀ z) = z :=
  LambertW.apply_mul_exp_apply_of_mem_domain trivial

theorem exists_eq_lambertW_of_eq_mul_exp (hw : z = w * cexp w) :
    ∃ k, w = W_ k z ∧ z ∈ domain k := by
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := eq_univ_iff_forall.mp iUnion_range w
  refine ⟨k, hw ▸ apply_mul_exp_of_mem_range hk |>.symm, ?_⟩
  by_cases hz : z = 0
  · rw [hz] at hw ⊢
    simp at hw
    simp [hw, zero_mem_range_iff] at hk
    simp [hk]
  by_cases hk : k = 0
  · simp [hk]
  · simpa [domain_of_ne_zero hk]

theorem eq_mul_exp_iff_exists_eq_lambertW :
    z = w * cexp w ↔ ∃ k, w = W_ k z ∧ z ∈ domain k := by
  refine ⟨exists_eq_lambertW_of_eq_mul_exp, fun ⟨k, hk, hz⟩ => ?_⟩
  rw [hk, apply_mul_exp_apply_of_mem_domain hz]

theorem existsUnique_eq_lambertW_of_ne_neg_inv_exp_one
    (hz : z ≠ -(exp 1)⁻¹) (hw : z = w * cexp w) : ∃! k, w = W_ k z ∧ z ∈ domain k := by
  sorry

/-- **TODO** doc -/
theorem conj_lambertW_eq_lambertW_neg_conj :
    conj (W_ k z) = W_ (-k) (conj z) := by
  sorry

theorem LambertW.isOpen_domain : IsOpen (domain k) := by
  change (if _ then _ else _ : Set ℂ) ∈ {y | IsOpen y}
  simp [ite_mem]

theorem LambertW.isOpen_slitPlane : IsOpen (slitPlane k) := by
  unfold slitPlane
  split_ifs with hk
  · exact isOpen_lt continuous_const continuous_re |>.union <|
      isOpen_ne_fun continuous_im continuous_const
  · exact Complex.isOpen_slitPlane

theorem LambertW.isClosed_branchCut : IsClosed (branchCut k) :=
  isOpen_slitPlane.isClosed_compl

theorem LambertW.isOpen_openRange : IsOpen (openRange k) := by
  sorry

theorem _root_.continuousAt_clambertW {z : ℂ} (h : z ∈ LambertW.slitPlane k) :
    ContinuousAt (W_ k) z := by
  sorry

theorem _root_.Filter.Tendsto.clambertW {l : Filter α} {f : α → ℂ} {x : ℂ} (h : Tendsto f l (𝓝 x))
    (hx : x ∈ LambertW.slitPlane k) : Tendsto (fun t => W_ k (f t)) l (𝓝 <| W_ k x) :=
  (continuousAt_clambertW hx).tendsto.comp h

variable [TopologicalSpace α]

nonrec theorem _root_.ContinuousAt.clambertW {f : α → ℂ} {x : α} (h₁ : ContinuousAt f x)
    (h₂ : f x ∈ LambertW.slitPlane k) : ContinuousAt (fun t => W_ k (f t)) x :=
  h₁.clambertW h₂

nonrec theorem _root_.ContinuousWithinAt.clambertW {f : α → ℂ} {s : Set α} {x : α}
    (h₁ : ContinuousWithinAt f s x) (h₂ : f x ∈ LambertW.slitPlane k) :
    ContinuousWithinAt (fun t => W_ k (f t)) s x :=
  h₁.clambertW h₂

nonrec theorem _root_.ContinuousOn.clambertW {f : α → ℂ} {s : Set α} (h₁ : ContinuousOn f s)
    (h₂ : ∀ x ∈ s, f x ∈ LambertW.slitPlane k) : ContinuousOn (fun t => W_ k (f t)) s :=
  fun x hx => (h₁ x hx).clambertW (h₂ x hx)

nonrec theorem _root_.Continuous.clambertW {f : α → ℂ} (h₁ : Continuous f)
    (h₂ : ∀ x, f x ∈ LambertW.slitPlane k) : Continuous fun t => W_ k (f t) :=
  continuous_iff_continuousAt.mpr fun x => h₁.continuousAt.clambertW (h₂ x)

/-- TODO doc -/
def mulExpOpenPartialHomeomorph : OpenPartialHomeomorph ℂ ℂ where
  toFun := fun w => w * cexp w
  invFun := lambertW k
  source := LambertW.openRange k
  target := LambertW.slitPlane k
  map_source' := by
    sorry
  map_target' z h := by
    sorry
  left_inv' _x hx := apply_mul_exp_of_mem_range <| openRange_subset_range hx
  right_inv' _x hx := apply_mul_exp_apply_of_mem_domain <| slitPlane_subset_domain hx
  open_source := isOpen_openRange
  open_target := LambertW.isOpen_slitPlane
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := continuousOn_id.clambertW fun _ => id

end LambertW

end Complex

namespace Real

open Set

variable {x y : ℝ}

/-- TODO doc -/
def lambertWZero : ℝ -> ℝ := fun x => (Complex.lambertW 0 x).re

/-- TODO doc -/
def lambertWNegOne : ℝ -> ℝ := fun x => (Complex.lambertW (-1) x).re

@[inherit_doc] scoped[RealLambertW] notation "W₀" => Real.lambertWZero
recommended_spelling "lambertWZero" for "W₀" in [lambertWZero, RealLambertW.«termW₀»]

@[inherit_doc] scoped[RealLambertW] notation "W₋₁" => Real.lambertWNegOne
recommended_spelling "lambertWNegOne" for "W₋₁" in [lambertWNegOne, RealLambertW.«termW₋₁»]

open scoped RealLambertW

/-- TODO doc -/
scoped[OmegaConstant] notation "Ω" => W₀ 1
recommended_spelling "omegaConstant" for "Ω" in [OmegaConstant.«termΩ»]

open scoped OmegaConstant

theorem bijOn_lambertWZero : BijOn W₀ (Ici (-(rexp 1)⁻¹)) (Ici (-1)) := by
  sorry

theorem bijOn_lambertWNegOne : BijOn W₋₁ (Iic (-(rexp 1)⁻¹)) (Iic (-1)) := by
  sorry

theorem lambertWZero_mul_exp_lambertWZero_of_le (hx : -(rexp 1)⁻¹ ≤ x) :
    W₀ x * rexp (W₀ x) = x := by
  sorry

theorem lambertWZero_mul_exp_of_le (hx : -1 ≤ x) : W₀ (x * rexp x) = x := by
  sorry

theorem lambertWNegOne_mul_exp_lambertWNegOne_of_le (hx : x ∈ Ico (-(rexp 1)⁻¹) 0) :
    W₋₁ x * rexp (W₋₁ x) = x := by
  sorry

theorem lambertWNegOne_mul_exp_of_le (hx : x ≤ -1) : W₋₁ (x * rexp x) = x := by
  sorry

theorem strictMonoOn_lambertWZero : StrictMonoOn W₀ (Ici (-(rexp 1)⁻¹)) := by
  sorry

theorem strictAntiOn_lambetWNegOne : StrictAntiOn W₋₁ (Ico (-(rexp 1)⁻¹) 0) := by
  sorry

@[simp]
theorem lambertWZero_zero : W₀ 0 = 0 := by

theorem lambertWZero_pos_of_pos (hx : 0 < x) : 0 < W₀ x := by
  rw [← lambertWZero_zero]
  have : -(rexp 1)⁻¹ ≤ 0 := by simpa using exp_nonneg 1
  apply strictMonoOn_lambertWZero this (this.trans hx.le) hx

theorem lambertWZero_nonneg_of_nonneg (hx : 0 ≤ x) : 0 ≤ W₀ x := by
  rw [← lambertWZero_zero]
  have : -(rexp 1)⁻¹ ≤ 0 := by simpa using exp_nonneg 1
  apply strictMonoOn_lambertWZero.monotoneOn this (this.trans hx) hx

theorem omegaConstant_lt_one : Ω < 1 := by
  sorry

open Qq Mathlib.Meta.Positivity in
/-- TODO doc -/
@[positivity Real.lambertWZero _]
meta def _root_.Mathlib.Meta.Positivity.evalLambertWZero : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(W₀ $a) =>
    assertInstancesCommute
    match ← core zα pα a with
    | .positive pa => pure <| .positive q(lambertWZero_pos_of_pos $pa)
    | .nonnegative pa => pure <| .nonnegative q(lambertWZero_nonneg_of_nonneg $pa)
    | _ => pure .none
  | _, _, _ => throwError "not Real.lambertWZero"

theorem zero_lt_omegaConstant : 0 < Ω := by
  positivity

theorem lambertWZero_add_lambertWZero_of_pos : W₀ x + W₀ y = W₀ (x * y / W₀ x + x * y / W₀ y) := by
  sorry

end Real

#lint
