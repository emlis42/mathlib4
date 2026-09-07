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

section LambertWAux

namespace Real

open Filter Topology Set

variable {x : ℝ}

private theorem exists_log_sub_eq_of_le_one (hx : x ≤ -1) :
    ∃ t ∈ Ioc 0 1, log t - t = x := by
  have hcont : ContinuousOn (fun t => log t - t) (Icc (rexp x) 1) :=
    continuousOn_log.mono (fun x hx => by grind [hx.1, exp_pos]) |>.sub continuousOn_id
  obtain ⟨t, ht, hteq⟩ : ∃ t ∈ Icc (rexp x) 1, log t - t = x :=
    intermediate_value_Icc (by grind [exp_le_one_iff]) hcont ⟨by linarith [exp_pos x, log_exp x],
      show x ≤ log 1 - 1 by grind [log_one]⟩
  exact ⟨t, ⟨by grind [ht.1, exp_pos], ht.2⟩, hteq⟩

theorem exists_log_add_eq (x : ℝ) : ∃ t > 0, log t + t = x := by
  --  use ContinuousOn.surjOn_of_tendsto ?
  exact continuousOn_log.add continuousOn_id |>.mono (by simp) |>.surjOn_of_tendsto
    nonempty_Ioi (tendsto_comp_coe_Ioi_atBot (Order.IsPredPrelimit.of_dense 0) |>.mpr <|
      tendsto_log_nhdsGT_zero.atBot_add <| tendsto_id.mono_left nhdsWithin_le_nhds)
        (tendsto_comp_val_Ioi_atTop.mpr <| tendsto_log_atTop.atTop_add_atTop tendsto_id) trivial
  -- obtain ⟨a, ha, ⟨ha₀, -⟩⟩ : ∃ a, log a + a < x ∧ a ∈ Ioo 0 1 :=
  --   tendsto_log_nhdsGT_zero.atBot_add (tendsto_id.mono_left nhdsWithin_le_nhds)
  --     |>.eventually_lt_atBot x |>.and (Ioo_mem_nhdsGT zero_lt_one) |>.exists
  -- obtain ⟨b, hb, hab⟩ : ∃ b, x < log b + b ∧ a < b  :=
  --   tendsto_log_atTop.atTop_add_atTop tendsto_id
  --     |>.eventually_gt_atTop x |>.and (eventually_gt_atTop a) |>.exists
  -- obtain ⟨t, ⟨hta, -⟩, ht⟩ :=
  --   intermediate_value_Icc hab.le
  --     (continuousOn_log.add continuousOn_id |>.mono <| fun t ht => by grind) ⟨ha.le, hb.le⟩
  -- exact ⟨t, ha₀.trans_le hta, ht⟩

private theorem eq_of_log_add_self_eq {t₁ t₂ : ℝ} (h₁ : 0 < t₁) (h₂ : 0 < t₂)
    (h : Real.log t₁ + t₁ = Real.log t₂ + t₂) : t₁ = t₂ :=
  (strictMonoOn_log.add strictMonoOn_id).injOn h₁ h₂ h

end Real

namespace Complex

open Real Set

open scoped ComplexConjugate

variable {x y : ℂ} {i : ℤ}

theorem im_pos_of_arg (h : x.arg ∈ Ioo 0 π) : 0 < x.im := by
  rw [← norm_mul_sin_arg]
  apply mul_pos (norm_pos_iff.mpr fun nh => ?_) <| sin_pos_of_mem_Ioo h
  simp [nh] at h

private theorem arg_add_im_eq_pi_of_arg_eq_pi (h : x.arg = π) : x.arg + x.im = π := by
  simpa [(arg_eq_pi_iff.1 h).2]

private theorem re_add_log_eq (x : ℂ) : (x + log x).re = Real.log ‖x‖ + ‖x‖ * Real.cos x.arg := by
  simp [Complex.log_re, add_comm]

private theorem add_log_re (w : ℂ) : (w + log w).re = Real.log ‖w‖ + w.re := by
  rw [Complex.add_re, Complex.log_re, add_comm]

private theorem re_add_log_le_neg_one {t : ℝ} (ht : 0 < t) : ((-t) + log (-t)).re ≤ -1 := by
  simp [log_re, abs_of_pos ht]
  linarith [log_le_sub_one_of_pos ht]

private theorem exp_add_log_of_ne_zero (hx : x ≠ 0) : cexp (x + x.log) = x * cexp x := by
  rw [exp_add, exp_log hx, mul_comm]

private theorem add_log_im : (x + x.log).im = x.arg + x.im := by
  simp [log, add_comm]

private theorem arg_neg_ofReal {x : ℝ} (hx : 0 < x) : (-x : ℂ).arg = π := by
  simpa [arg_eq_pi_iff]

private theorem neg_add_log_neg {x : ℝ} (hx : 0 < x) :
    (-x) + log (-x) = ⟨Real.log x - x, π⟩ := by
  refine ext ?_ ?_
  · simp [log_re, neg_add_eq_sub]
  · rw [add_log_im, arg_neg_ofReal hx, neg_im, ofReal_im, neg_zero, add_zero]

private theorem exists_add_log_eq_add_log (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x * cexp x = y * cexp y) :
    ∃ i : ℤ, x + x.log = y + y.log + i * (2 * π * I) := by
  rw [← exp_add_log_of_ne_zero hx, ← exp_add_log_of_ne_zero hy] at h
  exact exp_eq_exp_iff_exists_int.mp h

private theorem add_log_eq_of_add_log_eq
    (h : x + log x = y + log y + i * (2 * π * I)) :
    x.arg + x.im = y.arg + y.im + 2 * π * i := by
  have := congrArg im h
  nth_rw 2 [add_im] at this
  simp only [add_log_im] at this
  simp at this
  linarith

private theorem add_log_eq_of_mul_exp_eq_of_lt (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x * cexp x = y * cexp y) (hlt : |(x.arg + x.im) - (y.arg + y.im)| < 2 * π) :
    x + log x = y + log y := by
  obtain ⟨m, hm⟩ := exists_add_log_eq_add_log hx hy h
  rw [add_log_eq_of_add_log_eq hm, add_sub_cancel_left,
    abs_mul, abs_mul, abs_of_pos pi_pos, abs_of_pos zero_lt_two,
    mul_lt_iff_lt_one_right two_pi_pos] at hlt
  simp_all only [Int.abs_lt_one_iff.mp <| mod_cast hlt, Int.cast_zero, zero_mul, add_zero]

private theorem eq_of_add_log_eq_of_arg_add_im_pos (h₁ : x ≠ 0) (h₂ : y ≠ 0)
    (harg₁ : x.arg ≠ π) (h : x + log x = y + log y) (hA : 0 < x.arg + x.im) : x = y := by
  sorry
private theorem eq_of_add_log_eq (h₁ : x ≠ 0) (h₂ : y ≠ 0) (h : x + log x = y + log y)
    (hne : x.arg ≠ π) : x = y := by
  sorry
private theorem exists_neg_real_add_log_le (hx : x ∈ Iic (-1) ×ℂ {π}) :
    ∃ t ∈ Ioc (α := ℝ) 0 1, (-t) + log (-t) = x := by
  sorry
private theorem exists_add_log_eq_of_im_pos {z : ℂ} (him : 0 < z.im) (h : z.im ≠ π ∨ -1 < z.re) :
    ∃ w ≠ 0, w.arg ∈ Ioo 0 π ∧ w + log w = z := by
  sorry
private theorem exists_add_log_eq_of_abs_im_ne_pi {z : ℂ} (hz : |z.im| ≠ π ∨ -1 < z.re) :
    ∃ w ∈ Complex.slitPlane, w + log w = z := by
  rcases lt_trichotomy z.im 0 with him | him | him
  · have h' : (conj z).im = -z.im := by simp
    have hpos : 0 < (conj z).im := by rw [h']; linarith
    obtain ⟨w', hw', ⟨hw'l, hw'r⟩, hw'z⟩ : ∃ w ≠ 0, w.arg ∈ Ioo 0 π ∧ w + log w = conj z :=
      exists_add_log_eq_of_im_pos hpos (by simp_all [abs_of_neg him])
    refine ⟨conj w', ?_, ?_⟩
    · simp [mem_slitPlane_iff_arg, hw', arg_conj, hw'r.ne]
      linarith
    · rw [log_conj _ hw'r.ne, ← map_add, hw'z, conj_conj]
  · obtain ⟨t, ht, hteq⟩ := exists_log_add_eq z.re
    refine ⟨t, ?_, ?_⟩
    · simp [ht]
    · rw [Complex.ext_iff]
      simp [log_ofReal_re]
      simp [log, arg_ofReal_of_nonneg ht.le, him, ← hteq, add_comm]
  · obtain ⟨w, hw, ⟨hwl, hwr⟩, hwz⟩ : ∃ w ≠ 0, w.arg ∈ Ioo 0 π ∧ w + log w = z :=
      exists_add_log_eq_of_im_pos him (by simp_all [abs_of_pos him])
    use w, mem_slitPlane_iff_arg.mpr ⟨hwr.ne, hw⟩, hwz

end Complex

end LambertWAux

namespace Complex

open Real Set Filter Topology

open scoped ComplexConjugate

variable {α : Type*} {k : ℤ} {z w : ℂ}

section LambertWRangeDomain

section Definition

/-- TODO doc -/
def LambertW.branchCut (k : ℤ) : Set ℂ :=
  Iic (if k = 0 then -(rexp 1)⁻¹ else 0) ×ℂ {0}

private def LambertW.negRay : Set ℂ :=
  Iic (-1) ×ℂ {0}

/-- TODO doc -/
def LambertW.slitPlane (k : ℤ) : Set ℂ :=
  (branchCut k)ᶜ

-- /-- TODO doc, ref this? https://en.wikipedia.org/wiki/Quadratrix_of_Hippias -/
-- def LambertW.boundaryAux (k : ℤ) : Set ℂ :=
--   (fun t => ⟨-t * Real.cot t, t⟩) '' Ioo (k * π) ((k + 1) * π)

-- /-- TODO doc -/
-- def LambertW.upperBoundary (k : ℤ) : Set ℂ := match k with
--   | Int.ofNat (_ + 1) => LambertW.boundaryAux (2 * k)
--   | 0 => LambertW.boundaryAux 0 ∪ {-1}
--   | -1 => LambertW.branchCut 0 ∪ LambertW.boundaryAux (-1)
--   | Int.negSucc (_ + 1) => LambertW.boundaryAux (2 * k + 1)

-- /-- TODO doc -/
-- def LambertW.lowerBoundary (k : ℤ) : Set ℂ := match k with
--   | Int.ofNat (_ + 2) => LambertW.boundaryAux (2 * k - 2)
--   | 1 => LambertW.boundaryAux 0 ∪ {-1}
--   | 0 => LambertW.boundaryAux (-1)
--   | Int.negSucc _ => LambertW.boundaryAux (2 * k + 1)

/-- TODO doc -/
def LambertW.domain (k : ℤ) : Set ℂ :=
  if k = 0 then univ else {0}ᶜ

@[simp]
theorem LambertW.domain_zero : domain 0 = univ :=
  rfl

theorem LambertW.domain_of_ne_zero (hk : k ≠ 0) : domain k = {0}ᶜ :=
  ite_eq_right hk

/-- TODO doc -/
def LambertW.range (k : ℤ) : Set ℂ := match k with
  | 0 => {w | w.arg + w.im ∈ Ioc (-π) π} \ Iio (-1) ×ℂ {0}
  | -1 => {w | w.arg + w.im ∈ Ioc (-3 * π) (-π)} ∪ Iic (-1) ×ℂ {0}
  | _ => {w | w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π)}
  -- {w | LambertW.StrictAboveBoundary k w ∧ LambertW.BelowBondary k w} ∪ {w | w = -1 ∧ k = 0}

/-- TODO doc -/
def LambertW.openRange (k : ℤ) : Set ℂ := match k with
  | 0 => {w | w.arg + w.im ∈ Ioo (-π) π} ∪ {w | w.im = 0 ∧ w.re ∈ Ioo (-1) 0}
  | _ => {w | w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π)}
  -- {w | LambertW.StrictAboveBoundary k w ∧ LambertW.StrictBelowBondary k w}

end Definition

theorem LambertW.mem_domain_of_ne_zero (hz : z ≠ 0) : z ∈ domain k :=
  em (k = 0) |>.elim (fun hk => hk ▸ trivial) (fun hk => domain_of_ne_zero hk ▸ hz)

theorem LambertW.mem_range_zero_iff :
    w ∈ range 0 ↔ w.arg + w.im ∈ Ioc (-π) π ∧ ¬(w.re < -1 ∧ w.im = 0) := by
  simp [range, mem_reProdIm]

theorem LambertW.mem_range_neg_one_iff :
    w ∈ range (-1) ↔ w.arg + w.im ∈ Ioc (-3 * π) (-π) ∨ (w.re ≤ -1 ∧ w.im = 0) := by
  simp [range, mem_reProdIm]

theorem LambertW.mem_range_iff_of_ne (hk : k ≠ 0) (hk' : k ≠ -1) :
    w ∈ range k ↔ w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) := by
  simp [range]

theorem LambertW.zero_mem_range_zero : 0 ∈ range 0 := by
  simp [mem_range_zero_iff, pi_pos, pi_nonneg]

theorem LambertW.zero_notMem_range_neg_one : 0 ∉ range (-1) := by
  simp [range, mem_reProdIm]

theorem LambertW.zero_notMem_range (hk : k ≠ 0) : 0 ∉ range k := by
  by_cases hk' : k = -1
  · exact hk' ▸ zero_notMem_range_neg_one
  rw [mem_range_iff_of_ne hk hk', arg_zero, zero_im, add_zero]
  rcases (show k < -1 ∨ k > 0 by omega) with hk | hk
  · simpa using fun _ => mul_neg_of_neg_of_pos (mod_cast by omega) pi_pos
  · simp [mul_pos (show (0 : ℝ) < 2 * k - 1 from mod_cast by omega) pi_pos |>.not_gt]

@[simp]
theorem LambertW.zero_mem_range_iff : 0 ∈ range k ↔ k = 0 := by
  grind [zero_notMem_range, zero_mem_range_zero]

@[simp]
theorem LambertW.neg_one_mem_range_neg_one : -1 ∈ range (-1) := by
  simp [mem_range_neg_one_iff]

@[simp]
theorem LambertW.neg_one_mem_range_zero : -1 ∈ range 0 := by
  simp [mem_range_zero_iff, pi_pos]

private theorem LambertW.existsUnique_eq_pi_mul_exp_eq (hz : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0}) :
    ∃! w : ℂ, w.arg + w.im = π ∧ w * cexp w = z ∧ w.im > 0 := by
  sorry

private theorem LambertW.existsUnique_Ioo_exp_eq (hz : z ∈ Ioo (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    ∃! w : ℂ, w ∈ Ioo (-1) 0 ×ℂ {0} ∧ w * cexp w = z := by
  sorry

private theorem LambertW.existsUnique_eq_neg_pi_mul_exp_eq (hz : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0}) :
    ∃! w : ℂ, w.arg + w.im = -π ∧ w * cexp w = z := by
  sorry

private theorem LambertW.existsUnique_neg_exp_eq (hz : z ∈ Ioo (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    ∃! w : ℂ, w ∈ Iio (-1) ×ℂ {0} ∧ w * cexp w = z := by
  sorry

private theorem LambertW.existsUnique_eq_mul_exp_eq
    (hk : k ≠ 0) (hk' : k ≠ -1) (hz : z ∈ Iio 0 ×ℂ {0}) :
    ∃! w : ℂ, w.arg + w.im = (2 * k + 1) * π ∧ w * cexp w = z := by
  sorry

private theorem LambertW.exists_mem_Ioo_mul_exp_eq (k : ℤ) (hz : z ∈ Complex.slitPlane) :
    ∃ w : ℂ, w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π) ∧ w * cexp w = z := by
  sorry

private theorem LambertW.existsUnique_mem_Ioo_mul_exp_eq (k : ℤ) (hz : z ∈ Complex.slitPlane) :
    ∃! w : ℂ, w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π) ∧ w * cexp w = z := by
  obtain ⟨w, ⟨hwl, hwr⟩, hwz⟩ := exists_mem_Ioo_mul_exp_eq k hz
  use w, ⟨⟨hwl, hwr⟩, hwz⟩
  intro w' ⟨⟨hw'l, hw'r⟩, hw'z⟩
  have hz : z ≠ 0 := slitPlane_ne_zero hz
  have := add_log_eq_of_mul_exp_eq_of_lt (by grind) (by grind) (hwz ▸ hw'z)
    (by apply abs_sub_lt_iff.mpr ⟨?_, ?_⟩ <;> linarith)
  -- refine eq_of_add_log_eq_of_arg_add_im_pos (by grind) (by grind) ?_ this ?_

theorem LambertW.image_mul_exp_range_zero : (fun w => w * cexp w) '' range 0 = univ := by
  refine eq_univ_iff_forall.mpr fun z => ?_
  by_cases hz : z = 0
  · use 0; simp [hz]
  by_cases hz' : z ∈ Iio 0 ×ℂ {0}
  case neg =>
    replace hz : z ∈ Complex.slitPlane := by
      simp [Complex.ext_iff, mem_reProdIm, mem_slitPlane_iff] at hz hz' ⊢
      grind
    obtain ⟨w, ⟨⟨hwl, hwr⟩, hwz⟩, -⟩ := existsUnique_mem_Ioo_mul_exp_eq 0 hz
    simp only [Int.cast_zero, mul_zero, zero_sub, neg_mul, one_mul, zero_add,
      mem_image] at hwl hwr ⊢
    have hw' : w ∉ Iio (-1) ×ℂ {0} := by
      simp only [mem_reProdIm, mem_Iio, mem_singleton_iff, not_and]
      rintro hre him
      rw [arg_eq_pi_iff.mpr ⟨by linarith, him⟩, him, add_zero, lt_self_iff_false] at hwr
      exact hwr.elim
    use w, ⟨⟨hwl, hwr.le⟩, hw'⟩, hwz
  rcases lt_trichotomy z.re (-(rexp 1)⁻¹) with hz'' | hz'' | hz''
  · replace hz'' : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, ⟨hwl, hwz, hwr⟩, -⟩ := existsUnique_eq_pi_mul_exp_eq hz''
    simp only [mem_image, mem_range_zero_iff, mem_Ioc, not_and]
    use w, ⟨⟨by rw [hwl]; linarith [pi_pos], hwl.le⟩, by simp [hwr.ne']⟩, hwz
  · simp only [mem_reProdIm, mem_singleton_iff] at hz'
    use (-1 : ℝ)
    constructor
    · simp
    simp [-ofReal_neg, -ofReal_one, Complex.ext_iff, hz'', hz'.right, exp_ofReal_re, Real.exp_neg]
  · replace hz'' : z ∈ Ioo (-(rexp 1)⁻¹) 0 ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, ⟨hw, hwz⟩, -⟩ := existsUnique_Ioo_exp_eq hz''
    simp [mem_reProdIm] at hw
    have hw' : w.arg + w.im = π :=
      arg_add_im_eq_pi_of_arg_eq_pi <| arg_eq_pi_iff.mpr ⟨hw.left.right, hw.right⟩
    simp only [mem_image, mem_range_zero_iff, mem_Ioc, not_and]
    use w, ⟨⟨by linarith [pi_pos], hw'.le⟩, by simp [hw.left.left.not_gt]⟩, hwz

theorem LambertW.image_mul_exp_range_neg_one : (fun w => w * cexp w) '' range (-1) = {0}ᶜ := by
  refine eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    simp only [mem_compl_iff, mem_singleton_iff, mul_eq_zero, exp_ne_zero, or_false]
    rintro rfl
    simp_all
  intro z hz
  by_cases hz' : z ∈ Iio 0 ×ℂ {0}
  case neg =>
    replace hz : z ∈ Complex.slitPlane := by
      simp [Complex.ext_iff, mem_reProdIm, mem_slitPlane_iff] at hz hz' ⊢
      grind
    obtain ⟨w, ⟨⟨hwl, hwr⟩, hwz⟩, -⟩ := existsUnique_mem_Ioo_mul_exp_eq (-1) hz
    simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, mul_neg, mul_one, mem_image,
      mem_range_neg_one_iff, neg_mul, mem_Ioc] at hwl hwr ⊢
    use w, Or.inl ⟨by linarith, by linarith⟩, hwz
  rcases lt_trichotomy z.re (-(rexp 1)⁻¹) with hz'' | hz'' | hz''
  · replace hz : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, ⟨hw, hwz⟩, -⟩ := existsUnique_eq_neg_pi_mul_exp_eq hz
    simp only [Int.reduceNeg, mem_image, mem_range_neg_one_iff, neg_mul, mem_Ioc]
    use w, Or.inl ⟨by rw [hw]; linarith [pi_pos], hw.le⟩, hwz
  · simp only [mem_reProdIm, mem_singleton_iff] at hz'
    use (-1 : ℝ)
    constructor
    · simp
    simp [-ofReal_neg, -ofReal_one, Complex.ext_iff, hz'', hz'.right, exp_ofReal_re, Real.exp_neg]
  · replace hz : z ∈ Ioo (-(rexp 1)⁻¹) 0 ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, ⟨hw, hwz⟩, -⟩ := existsUnique_neg_exp_eq hz
    simp only [Int.reduceNeg, mem_image, mem_range_neg_one_iff, neg_mul, mem_Ioc]
    simp only [mem_reProdIm, mem_Iio, mem_singleton_iff] at hw
    use w, Or.inr ⟨hw.left.le, hw.right⟩, hwz

theorem LambertW.image_mul_exp_range_of_ne_zero (hk : k ≠ 0) (hk' : k ≠ -1) :
    (fun w => w * cexp w) '' range k = {0}ᶜ := by
  refine eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    simp only [mem_compl_iff, mem_singleton_iff, mul_eq_zero, exp_ne_zero, or_false]
    rintro rfl
    simp_all
  intro z hz
  suffices ∃ w : ℂ, w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) ∧ w * cexp w = z by
    obtain ⟨w, ⟨hwl, hwr⟩, hwz⟩ := this
    simp only [mem_image, mem_range_iff_of_ne hk hk', mem_Ioc]
    use w
  by_cases hz' : z ∈ Iio 0 ×ℂ {0}
  · obtain ⟨w, ⟨hw, hwz⟩, -⟩ := existsUnique_eq_mul_exp_eq hk hk' hz'
    use w, ⟨by rw [hw]; linarith [pi_pos], hw.le⟩, hwz
  · replace hz : z ∈ Complex.slitPlane := by
      simp [Complex.ext_iff, mem_reProdIm, mem_slitPlane_iff] at hz hz' ⊢
      grind
    obtain ⟨w, ⟨⟨hwl, hwr⟩, hwz⟩, -⟩ := existsUnique_mem_Ioo_mul_exp_eq k hz
    use w, ⟨hwl, hwr.le⟩, hwz

theorem LambertW.image_mul_exp_range :
    (fun w => w * cexp w) '' range k = domain k := by
  by_cases hk : k = 0
  · rw [hk, image_mul_exp_range_zero, domain_zero]
  by_cases hk : k = -1
  · rw [hk, image_mul_exp_range_neg_one, domain_of_ne_zero (by simp)]
  · rw [image_mul_exp_range_of_ne_zero ‹_› ‹_›, domain_of_ne_zero ‹_›]

theorem LambertW.mapsTo_mul_exp_range :
    MapsTo (fun w => w * cexp w) (range k) (domain k) := by
  simpa only [← image_mul_exp_range] using mapsTo_image _ _

theorem LambertW.mapsTo_mul_exp_range_zero :
    MapsTo (fun w => w * cexp w) (range 0) univ := by
  simpa only [← domain_zero] using mapsTo_mul_exp_range

theorem LambertW.mapsTo_mul_exp_range_of_ne_zero (hk : k ≠ 0) :
    MapsTo (fun w => w * cexp w) (range k) {0}ᶜ := by
  simpa only [← domain_of_ne_zero hk] using mapsTo_mul_exp_range

private theorem LambertW.injOn_mul_exp_range_zero :
    InjOn (fun w => w * cexp w) (range 0) := by
  intro w₁ hw₁ w₂ hw₂ (h : w₁ * cexp w₁ = w₂ * cexp w₂)
  rw [mem_range_zero_iff] at hw₁ hw₂
  set z := w₁ * cexp w₁ with hz₁
  have hz₂ : z = w₂ * cexp w₂ := h ▸ hz₁
  by_cases hz : z = 0
  · simp_all
  by_cases hz' : z ∈ Iio 0 ×ℂ {0}
  case neg =>
    replace hz : z ∈ Complex.slitPlane := by
      simp [Complex.ext_iff, mem_reProdIm, mem_slitPlane_iff] at hz hz' ⊢
      grind
    obtain ⟨w, -, hw⟩ := existsUnique_mem_Ioo_mul_exp_eq 0 hz
    simp only [Int.cast_zero, mul_zero, zero_sub, neg_mul, one_mul, zero_add] at hw
    have hw₁' : w₁.arg + w₁.im < π := by
      sorry
    have hw₂' : w₂.arg + w₂.im < π := by
      sorry
    have Hw₁ := hw w₁ ⟨⟨hw₁.left.left, hw₁'⟩, hz₁.symm⟩
    have Hw₂ := hw w₂ ⟨⟨hw₂.left.left, hw₂'⟩, hz₂.symm⟩
    exact Hw₂ ▸ Hw₁
  rcases lt_trichotomy z.re (-(rexp 1)⁻¹) with hz'' | hz'' | hz''
  · replace hz'' : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, -, hw⟩ := existsUnique_eq_pi_mul_exp_eq hz''
    have Hw₁ := hw w₁
    sorry
  · sorry
  · sorry

private theorem LambertW.injOn_mul_exp_range_neg_one :
    InjOn (fun w => w * cexp w) (range (-1)) := by
  sorry

private theorem LambertW.injOn_mul_exp_range_of_ne (hk : k ≠ 0) (hk' : k ≠ -1) :
    InjOn (fun w => w * cexp w) (range k) := by
  sorry

theorem LambertW.injOn_mul_exp_range :
    InjOn (fun w => w * cexp w) (range k) := by
  rcases (show k = 0 ∨ k = -1 ∨ (k ≠ 0 ∧ k ≠ -1) by omega) with rfl | rfl | ⟨hk, hk'⟩
  · exact injOn_mul_exp_range_zero
  · exact injOn_mul_exp_range_neg_one
  · exact injOn_mul_exp_range_of_ne hk hk'

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

theorem LambertW.bijOn_mul_exp_range_zero :
    BijOn (fun w => w * cexp w) (range 0) univ := by
  simpa only [← domain_zero] using bijOn_mul_exp_range_domain

theorem LambertW.bijOn_mul_exp_range_of_ne_zero (hk : k ≠ 0) :
    BijOn (fun w => w * cexp w) (range k) {0}ᶜ := by
  simpa only [← domain_of_ne_zero hk] using bijOn_mul_exp_range_domain

theorem LambertW.iUnion_range : ⋃ k, range k = univ := by
  sorry

theorem LambertW.neg_one_notMem_range_of_ne : k ≠ 0 ∧ k ≠ (-1) -> -1 ∉ range k := by
  sorry

theorem LambertW.range_inter_eq_empty {i j : ℤ} (h1 : i ≠ j) (h2 : ({i, j} : Finset ℤ) ≠ {0, -1}) :
    range i ∩ range j = ∅ := by
  simp at h2
  sorry

theorem LambertW.existsUnique_mem_range_of_ne_neg_one (hw : w ≠ -1) :
    ∃! k, w ∈ range k := by
  sorry

theorem LambertW.openRange_subset_range : openRange k ⊆ range k := by
  grind [belowBondary_of_strictBelowBondary, openRange, range]

theorem LambertW.slitPlane_subset_domain : slitPlane k ⊆ domain k := by
  unfold slitPlane domain
  split_ifs with hk <;> simp [branchCut, hk, mem_reProdIm]

theorem LambertW.interior_range : interior (range k) = openRange k := by
  sorry

end LambertWRangeDomain

section LambertW

open LambertW

/-- TODO doc -/
@[pp_nodot]
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

theorem LambertW.isClosed_branchCut : IsClosed (branchCut k) :=
  isClosed_Iic.reProdIm isClosed_singleton

theorem LambertW.isOpen_slitPlane : IsOpen (slitPlane k) :=
  isClosed_branchCut.isOpen_compl

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
