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

open Real Set

open scoped ComplexConjugate

variable {k : ℤ} {z w : ℂ}

section LambertWRange

private def belowBondary (k : ℤ) (w : ℂ) : Prop :=
  ∃ η ∈ Ioo (k * π) ((k + 1) * π), w.re = -η * Real.cot η ∧ w.im ≤ η

private def aboveBoundary (k : ℤ) (w : ℂ) : Prop :=
  ∃ η ∈ Ioo (k * π) ((k + 1) * π), w.re = -η * Real.cot η ∧ w.im > η

/-- TODO doc -/
@[no_expose] def lambertWRange (k : ℤ) : Set ℂ := match k with
  | Int.ofNat (_ + 2) => { w | belowBondary (2 * k) w ∧ aboveBoundary (2 * k - 2) w }
  | 1 => { w | belowBondary 2 w ∧ (w.re ≤ -1 ∧ w.im > 0 ∨ aboveBoundary 0 w) }
  | 0 => { w | w = -1 ∨ belowBondary 0 w ∧ aboveBoundary (-1) w }
  | -1 => { w | aboveBoundary (-3) w ∧ (w.re ≤ -1 ∧ w.im ≤ 0 ∨ belowBondary (-1) w) }
  | Int.negSucc (_ + 1) => { w | aboveBoundary (2 * k - 1) w ∧ belowBondary (2 * k + 1) w }

/-- TODO doc -/
def lambertWDomain (k : ℤ) : Set ℂ :=
  if k = 0 then univ else {0}ᶜ

private theorem lambertWRange_of_one_lt {hk : 1 < k} :
    lambertWRange k = { w | belowBondary (2 * k) w ∧ aboveBoundary (2 * k - 2) w } := by
  match k with | Int.ofNat (_ + 2) => rfl

private theorem lambertWRange_one :
    lambertWRange 1 = { w | belowBondary 2 w ∧ (w.re ≤ -1 ∧ w.im > 0 ∨ aboveBoundary 0 w) } :=
  rfl

private theorem lambertWRange_zero :
    lambertWRange 0 = { w | w = -1 ∨ belowBondary 0 w ∧ aboveBoundary (-1) w } :=
  rfl

private theorem lambertWRange_neg_one :
    lambertWRange (-1) =
      { w | aboveBoundary (-3) w ∧ (w.re ≤ -1 ∧ w.im ≤ 0 ∨ belowBondary (-1) w) } :=
  rfl

private theorem lambertWRange_of_lt_neg_one {hk : k < -1} :
    lambertWRange k = { w | aboveBoundary (2 * k - 1) w ∧ belowBondary (2 * k + 1) w } := by
  match k with | Int.negSucc (_ + 1) => rfl

@[simp]
theorem lambertWDomain_zero : lambertWDomain 0 = univ :=
  rfl

theorem lambertWDomain_of_ne_zero (hk : k ≠ 0) : lambertWDomain k = {0}ᶜ :=
  ite_eq_right hk

theorem mem_lambertWDomain_of_ne_zero (hz : z ≠ 0) : z ∈ lambertWDomain k :=
  em (k = 0) |>.elim (fun hk => hk ▸ trivial) (fun hk => lambertWDomain_of_ne_zero hk ▸ hz)

theorem mul_exp_lambertWRange_zero : (fun w => w * cexp w) '' lambertWRange 0 = univ := by
  refine eq_univ_iff_forall.mpr fun w => ?_
  simp
  sorry

theorem mul_exp_lambertWRange_of_ne_zero (hk : k ≠ 0) :
    (fun w => w * cexp w) '' lambertWRange k = {0}ᶜ := by
  sorry

theorem mapsTo_mul_exp_lambertWRange_zero :
    MapsTo (fun w => w * cexp w) (lambertWRange 0) univ := by
  simpa only [← mul_exp_lambertWRange_zero] using mapsTo_image _ _

theorem mapsTo_mul_exp_lambertWRange_of_ne_zero (hk : k ≠ 0) :
    MapsTo (fun w => w * cexp w) (lambertWRange k) {0}ᶜ := by
  simpa only [← mul_exp_lambertWRange_of_ne_zero hk] using mapsTo_image _ _

theorem injOn_mul_exp_lambertWRange :
    InjOn (fun w => w * cexp w) (lambertWRange k) := by
  sorry

theorem surjOn_mul_exp_lambertWRange_zero :
    SurjOn (fun w => w * cexp w) (lambertWRange 0) univ := by
  simpa only [← mul_exp_lambertWRange_zero] using surjOn_image _ _

theorem surjOn_mul_exp_lambertWRange_of_ne_zero (hk : k ≠ 0) :
    SurjOn (fun w => w * cexp w) (lambertWRange k) {0}ᶜ := by
  simpa only [← mul_exp_lambertWRange_of_ne_zero hk] using surjOn_image _ _

theorem bijOn_mul_exp_lambertWRange_zero :
    BijOn (fun w => w * cexp w) (lambertWRange 0) univ :=
  ⟨ mapsTo_mul_exp_lambertWRange_zero, injOn_mul_exp_lambertWRange,
    surjOn_mul_exp_lambertWRange_zero ⟩

theorem bijOn_mul_exp_lambertWRange_of_ne_zero (hk : k ≠ 0) :
    BijOn (fun w => w * cexp w) (lambertWRange k) {(0 : ℂ)}ᶜ :=
  ⟨ mapsTo_mul_exp_lambertWRange_of_ne_zero hk, injOn_mul_exp_lambertWRange,
    surjOn_mul_exp_lambertWRange_of_ne_zero hk ⟩

theorem bijOn_mul_exp_lambertWRange_lambertWDomain :
    BijOn (fun w => w * cexp w) (lambertWRange k) (lambertWDomain k) := by
  by_cases hk : k = 0
  · simpa [hk] using bijOn_mul_exp_lambertWRange_zero
  · simpa [hk, lambertWDomain_of_ne_zero] using bijOn_mul_exp_lambertWRange_of_ne_zero hk

theorem iUnion_lambertWRange : ⋃ k, lambertWRange k = univ := by
  sorry

theorem neg_one_mem_lambertWRange_inter : -1 ∈ lambertWRange 0 ∩ lambertWRange (-1) := by
  rw [lambertWRange_zero, lambertWRange_neg_one]
  sorry

theorem neg_one_mem_lambertWRange_zero : -1 ∈ lambertWRange 0 :=
  neg_one_mem_lambertWRange_inter.left

theorem neg_one_mem_lambertWRange_neg_one : -1 ∈ lambertWRange (-1) :=
  neg_one_mem_lambertWRange_inter.right

theorem neg_one_not_mem_lambertWRange_of_ne : k ≠ 0 ∧ k ≠ (-1) -> -1 ∉ lambertWRange k := by
  sorry

theorem lambertWRange_inter_eq_empty {i j : ℤ} (h1 : i ≠ j) (h2 : ({i, j} : Finset ℤ) ≠ {0, -1}) :
    lambertWRange i ∩ lambertWRange j = ∅ := by
  simp at h2
  sorry

theorem existsUnique_mem_lambertWRange_of_ne_neg_one (hw : w ≠ -1) : ∃! k, w ∈ lambertWRange k := by
  sorry

theorem zero_mem_lambertWRange_iff : 0 ∈ lambertWRange k ↔ k = 0 := by
  sorry

end LambertWRange

section LambertW

/-- TODO doc -/
def lambertW (k : ℤ) : ℂ -> ℂ :=
  Function.invFunOn (fun w => w * cexp w) (lambertWRange k)

@[inherit_doc] scoped[ComplexLambertW] notation "W_ " => Complex.lambertW
recommended_spelling "lambertW" for "W_" in [lambertW, ComplexLambertW.«termW_»]

open scoped ComplexLambertW

/-- TODO doc -/
scoped[ComplexLambertW] notation "W₀" => W_ 0
recommended_spelling "lambertW_zero" for "W₀" in [ComplexLambertW.«termW₀»]

/-- TODO doc -/
scoped[ComplexLambertW] notation "W₋₁" => W_ (-1)
recommended_spelling "lambertW_neg_one" for "W₋₁" in [ComplexLambertW.«termW₋₁»]

theorem lambertW_mem_lambertWRange_of_mem_lambertWDomain
    (hz : z ∈ lambertWDomain k) : W_ k z ∈ lambertWRange k := by
  refine Function.invFunOn_mem ?_
  rwa [← mem_image, bijOn_mul_exp_lambertWRange_lambertWDomain.image_eq]

theorem lambertW_zero_mem_lambertWRange : W₀ z ∈ lambertWRange 0 :=
  lambertW_mem_lambertWRange_of_mem_lambertWDomain trivial

theorem lambertW_mul_exp_of_mem_lambertWRange (hw : w ∈ lambertWRange k) : W_ k (w * exp w) = w :=
  bijOn_mul_exp_lambertWRange_lambertWDomain.invOn_invFunOn.left hw

theorem lambertW_mul_exp_lambertW_of_mem_lambertWDomain (hz : z ∈ lambertWDomain k) :
    W_ k z * cexp (W_ k z) = z := by
  apply Function.invFunOn_eq (f := fun w => w * exp w)
  rwa [← mem_image, bijOn_mul_exp_lambertWRange_lambertWDomain.image_eq]

theorem lambertW_zero_mul_exp_lambertW_zero : W₀ z * cexp (W₀ z) = z :=
  lambertW_mul_exp_lambertW_of_mem_lambertWDomain trivial

theorem exists_eq_lambertW_of_eq_mul_exp (hw : z = w * cexp w) :
    ∃ k, w = W_ k z ∧ z ∈ lambertWDomain k := by
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := eq_univ_iff_forall.mp iUnion_lambertWRange w
  refine ⟨k, hw ▸ lambertW_mul_exp_of_mem_lambertWRange hk |>.symm, ?_⟩
  by_cases hz : z = 0
  · rw [hz] at hw ⊢
    simp at hw
    simp [hw, zero_mem_lambertWRange_iff] at hk
    simp [hk]
  by_cases hk : k = 0
  · simp [hk]
  · simpa [lambertWDomain_of_ne_zero hk]

theorem eq_mul_exp_iff_exists_eq_lambertW :
    z = w * cexp w ↔ ∃ k, w = W_ k z ∧ z ∈ lambertWDomain k := by
  refine ⟨exists_eq_lambertW_of_eq_mul_exp, fun ⟨k, hk, hz⟩ => ?_⟩
  rw [hk, lambertW_mul_exp_lambertW_of_mem_lambertWDomain hz]

private theorem eq_neg_one_of_mul_exp_eq_neg_inv_exp_one
    (hw : w * cexp w = -(exp 1)⁻¹) : w = -1 := by
  sorry

theorem mul_exp_eq_neg_inv_exp_one_iff_eq_neg_one : w * cexp w = -(exp 1)⁻¹ ↔ w = -1 :=
  ⟨eq_neg_one_of_mul_exp_eq_neg_inv_exp_one, by simp +contextual [exp_neg]⟩

theorem existsUnique_eq_lambertW_of_ne_neg_inv_exp_one
    (hz : z ≠ -(exp 1)⁻¹) (hw : z = w * cexp w) : ∃! k, w = W_ k z ∧ z ∈ lambertWDomain k := by
  sorry

theorem conj_lambertW_eq_lambertW_neg_conj :
    conj (W_ k z) = W_ (-k) (conj z) := by
  sorry

end LambertW

end Complex

namespace Real

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
recommended_spelling "omega" for "Ω" in [OmegaConstant.«termΩ»]

open scoped OmegaConstant

theorem lambertWZero_add_lambertWZero_of_pos : W₀ x + W₀ y = W₀ (x * y / W₀ x + x * y / W₀ y) := by
  sorry

end Real

#lint
