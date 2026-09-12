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

private theorem existsUnique_mem_Ioc (x : ℝ) :
    ∃! k : ℤ, x ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) := by
  simpa [mul_comm, mul_two, mul_sub, mul_add, add_comm, sub_lt_iff_lt_add] using
    existsUnique_sub_zsmul_mem_Ioc (a := 2 * π) two_pi_pos x (-π)

private theorem add_sin_mem_Ioo_of_mem_Ioo :
    ∀ ⦃x : ℝ⦄, x ∈ Ioo (-π) π -> x + x.sin ∈ Ioo (-π) π := by
  suffices ∀ x ∈ Ioo (-π) π, x + x.sin < π from fun x ⟨hxl, hxr⟩ =>
    ⟨by grind [this (-x) ⟨neg_lt_neg_iff.mpr hxr, neg_lt.mp hxl⟩, sin_neg x], this x ⟨hxl, hxr⟩⟩
  exact fun x hx => by grind [sin_lt <| sub_pos_of_lt hx.right, sin_pi_sub x]

-- private theorem exists_mem_Ioc_log_sub_eq_of_le_one (hx : x ≤ -1) :
--     ∃ t ∈ Ioc 0 1, log t - t = x := by
--   have hcont : ContinuousOn (fun t => log t - t) (Icc (rexp x) 1) :=
--     continuousOn_log.mono (fun x hx => by grind [hx.1, exp_pos]) |>.sub continuousOn_id
--   obtain ⟨t, ht, hteq⟩ : ∃ t ∈ Icc (rexp x) 1, log t - t = x :=
--     intermediate_value_Icc (by grind [exp_le_one_iff]) hcont ⟨by grind [exp_pos x, log_exp x],
--       show x ≤ log 1 - 1 by grind [log_one]⟩
--   exact ⟨t, ⟨by grind [ht.1, exp_pos], ht.2⟩, hteq⟩

private theorem existsUnique_mem_Ico_mul_exp_eq_of_mem_Ico (hx : x ∈ Ico (-(rexp 1)⁻¹) 0) :
    ∃! t ∈ Ico (-1) 0, t * rexp t = x := by
  obtain ⟨t, ht, hteq⟩ : ∃ t ∈ Icc (-1) 0, t * rexp t = x :=
    intermediate_value_Icc (by norm_num) (by fun_prop) ⟨by grind [exp_neg], by simpa using hx.2.le⟩
  exact ⟨t, ⟨⟨ht.left, by grind⟩, hteq⟩, fun y hy => exp_injective (mul_log_strictMonoOn.injOn
    (exp_le_exp.mpr hy.left.left) (exp_le_exp.mpr ht.left) (by grind [log_exp]))⟩

private theorem existsUnique_mem_Iic_mul_exp_eq_of_mem_Ico (hx : x ∈ Ico (-(rexp 1)⁻¹) 0) :
    ∃! t ∈ Iic (-1), t * rexp t = x := by
  obtain ⟨S, hS⟩ := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 |>.eventually <|
    eventually_lt_nhds <| neg_pos_of_neg hx.right).exists_forall_of_atTop
  obtain ⟨t, ht, hteq⟩ : ∃ t ∈ Icc (-(S ⊔ 1)) (-1), t * rexp t = x :=
    intermediate_value_Icc' (by simp) (by fun_prop)
      ⟨by grind [exp_neg], by grind [hS (S ⊔ 1), pow_one, exp_neg]⟩
  exact ⟨t, ⟨ht.2, hteq⟩, fun y hy => exp_injective <| mul_log_strictAntiOn.injOn
    ⟨exp_nonneg y, exp_le_exp.mpr hy.left⟩ ⟨exp_nonneg t, exp_le_exp.mpr ht.right⟩
      (by grind [log_exp])⟩

private theorem exists_add_log_eq (x : ℝ) : ∃ t > 0, t + log t = x :=
  continuousOn_id.add continuousOn_log |>.mono (by simp) |>.surjOn_of_tendsto
    nonempty_Ioi (tendsto_comp_coe_Ioi_atBot (Order.IsPredPrelimit.of_dense 0) |>.mpr <|
      tendsto_id.mono_left nhdsWithin_le_nhds |>.add_atBot tendsto_log_nhdsGT_zero)
        (tendsto_comp_val_Ioi_atTop.mpr <| tendsto_id.atTop_add_atTop tendsto_log_atTop) trivial

private theorem existsUnique_add_log_eq (x : ℝ) : ∃! t > 0, t + log t = x := by
  apply existsUnique_of_exists_of_unique (exists_add_log_eq x) fun t u ⟨ht, ht_eq⟩ ⟨hu, hu_eq⟩ => ?_
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h <;> [grind [log_lt_log ht h]; grind [log_lt_log hu h]]

-- private theorem eq_of_log_add_self_eq {t₁ t₂ : ℝ} (h₁ : 0 < t₁) (h₂ : 0 < t₂)
--     (h : Real.log t₁ + t₁ = Real.log t₂ + t₂) : t₁ = t₂ :=
--   (strictMonoOn_log.add strictMonoOn_id).injOn h₁ h₂ h

private theorem neg_exp_one_inv_le_mul_exp : -(rexp 1)⁻¹ ≤ x * rexp x := by
  grind [mul_exp_neg_le_exp_neg_one (-x), exp_neg]

end Real

namespace Complex

open Real Set

open scoped ComplexConjugate

variable {x y w z : ℂ} {i : ℤ}

theorem arg_neg_ofReal_of_pos {x : ℝ} (hx : 0 < x) : (-x : ℂ).arg = π := by
  rw [← ofReal_neg, arg_ofReal_of_neg <| neg_neg_iff_pos.mpr hx]

private theorem arg_add_im_eq_pi_of_arg_eq_pi (h : x.arg = π) : x.arg + x.im = π := by
  simpa [(arg_eq_pi_iff.1 h).2]

private theorem im_eq_zero_of_arg_add_im_eq_zero (hx : x.arg + x.im = 0) : x.im = 0 := by
  grind [arg_neg_iff]

theorem exists_arg_mul_eq_add_arg (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ k : ℤ, (x * y).arg = x.arg + y.arg + k * (2 * π):= by
  have h : ((x * y).arg : Real.Angle) = ((x.arg + y.arg : ℝ) : Real.Angle) := by
    rw [arg_mul_coe_angle hx hy, Angle.coe_add]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h
  exact ⟨k, by linarith⟩

private theorem arg_add_im_eq_arg_add_of_eq (hz : z ≠ 0) (hwz : w * cexp w = z) :
    ∃ k : ℤ, w.arg + w.im = z.arg + k * (2 * π) := by
  have hw : w ≠ 0 := by grind
  rw [← exp_log (show w * cexp w ≠ 0 from hwz ▸ hz), ← exp_log hz] at hwz
  rw [exp_eq_exp_iff_exists_int] at hwz
  obtain ⟨m, hm⟩ := hwz
  obtain ⟨n, hn⟩ := exists_arg_mul_eq_add_arg hw (exp_ne_zero w)
  apply congrArg im at hm
  replace hm : w.arg + toIocMod two_pi_pos (-π) w.im + n * (2 * π) = z.arg + m * (2 * π) := by
    simpa [log_im, hn, arg_exp] using hm
  unfold toIocMod at hm
  use m - n + toIocDiv two_pi_pos (-π) w.im
  grind

private theorem arg_pos_of_arg_add_im_pos (h : 0 < w.arg + w.im) : 0 < w.arg := by
  rcases lt_trichotomy w.arg 0 with h | h | h
  · linarith [arg_neg_iff.mp h]
  · linarith [arg_eq_zero_iff.mp h |>.right]
  · exact h

private theorem arg_mem_Ioo_of_arg_add_im_pos (hw : w ≠ 0)
    (harg : w.arg ≠ π) (hA : 0 < w.arg + w.im) : w.arg ∈ Ioo 0 (min (w.arg + w.im) π) := by
  replace harg : w.arg < π := lt_of_le_of_ne (arg_le_pi w) harg
  have harg₀ : 0 < w.arg := arg_pos_of_arg_add_im_pos hA
  refine ⟨harg₀, lt_min ?_ harg⟩
  rw [← norm_mul_sin_arg]
  nlinarith [Real.sin_pos_of_pos_of_lt_pi harg₀ harg, norm_pos_iff.mpr hw]

private theorem sin_arg_ne_zero_of_arg_add_im_pos
    (hw : w ≠ 0) (harg : w.arg ≠ π) (hA : 0 < w.arg + w.im) : Real.sin w.arg ≠ 0 := by
  obtain ⟨h0, h1⟩ := arg_mem_Ioo_of_arg_add_im_pos hw harg hA
  exact (Real.sin_pos_of_pos_of_lt_pi h0 <| h1.trans_le <| min_le_right _ _).ne'

private theorem exp_add_log_of_ne_zero (hx : x ≠ 0) : cexp (x + x.log) = x * cexp x := by
  rw [exp_add, exp_log hx, mul_comm]

private theorem add_log_im : (x + x.log).im = x.arg + x.im := by
  simp [log, add_comm]

private theorem exists_add_log_eq_add_log (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x * cexp x = y * cexp y) :
    ∃ i : ℤ, x + x.log = y + y.log + i * (2 * π * I) := by
  rw [← exp_add_log_of_ne_zero hx, ← exp_add_log_of_ne_zero hy] at h
  exact exp_eq_exp_iff_exists_int.mp h

private theorem add_log_eq_of_add_log_eq
    (h : x + log x = y + log y + i * (2 * π * I)) :
    x.arg + x.im = y.arg + y.im + i * (2 * π) := by
  have := congrArg im h
  nth_rw 2 [add_im] at this
  simp only [add_log_im] at this
  simp at this
  linarith

private theorem add_log_eq_of_mul_exp_eq_of_lt (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x * cexp x = y * cexp y) (hlt : |(x.arg + x.im) - (y.arg + y.im)| < 2 * π) :
    x + log x = y + log y := by
  obtain ⟨m, hm⟩ := exists_add_log_eq_add_log hx hy h
  rw [add_log_eq_of_add_log_eq hm, add_sub_cancel_left, abs_mul, abs_mul, abs_of_pos pi_pos,
    abs_of_pos (a := 2) zero_lt_two, mul_lt_iff_lt_one_left two_pi_pos] at hlt
  simp_all only [Int.abs_lt_one_iff.mp <| mod_cast hlt, Int.cast_zero, zero_mul, add_zero]

private theorem arg_add_im_eq_of_mul_exp_eq_mem (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x * cexp x = y * cexp y) (hx' : x.arg + x.im ∈ Ioc ((2 * i - 1) * π) ((2 * i + 1) * π))
      (hy' : y.arg + y.im ∈ Ioc ((2 * i - 1) * π) ((2 * i + 1) * π)) :
    x.arg + x.im = y.arg + y.im := by
  have := add_log_eq_of_mul_exp_eq_of_lt hx hy h (by apply abs_sub_lt_iff.mpr ⟨?_, ?_⟩ <;> grind)
  apply congrArg im at this
  simpa [log_im, add_comm] using this

private theorem arg_mul_exp_eq_of_mem {x : ℂ} {i : ℤ} (hx : x ≠ 0)
    (h : x.arg + x.im ∈ Ioc ((2 * i - 1) * π) ((2 * i + 1) * π)) :
    (x * cexp x).arg = x.arg + x.im - i * (2 * π) := by
  rw [← exp_log hx, ← exp_add, mul_comm, arg_exp, add_im, log_im, toIocMod_eq_iff, exp_log hx]
  exact ⟨by grind [h.left, h.right, Real.pi_pos], i, by ring⟩

private theorem mul_exp_mem_of_arg_add_im_eq {w : ℂ} {i : ℤ}
    (hw : w.arg + w.im ∈ Ioc ((2 * i - 1) * π) ((2 * i + 1) * π))
    (hz : w * cexp w ∈ Iio 0 ×ℂ {0}) : w.arg + w.im = (2 * i + 1) * π := by
  grind [arg_mul_exp_eq_of_mem (fun nh => by simp [nh, mem_reProdIm] at hz) hw,
    arg_eq_pi_iff.mpr hz]

private theorem exp_add_log (hw : w ≠ 0) : exp (w + log w) = w * exp w := by
  rw [add_comm, exp_add, exp_log hw]

private theorem mul_exp_eq_of_arg_add_im_eq (hx : x ≠ 0) (h : x.arg + x.im = (2 * i + 1) * π) :
    x * cexp x = -rexp (x + log x).re := by
  rw [← exp_add_log hx]
  apply Complex.ext
  · rw [exp_re, add_log_im, h, show (2 * i + 1) * π = i * (2 * π) + π by ring,
      Real.cos_int_mul_two_pi_add_pi i, neg_re, ofReal_re, mul_neg_one]
  · rw [exp_im, add_log_im, h, show (2 * i + 1) * π = (2 * i + 1 : ℤ) * π by norm_cast,
      Real.sin_int_mul_pi _, mul_zero, neg_im, ofReal_im, neg_zero]

private theorem mul_exp_mem_of_im_eq_zero (hw : w.im = 0) :
    w * cexp w ∈ Ici (-(rexp 1)⁻¹) ×ℂ {0} := by
  simpa [mem_reProdIm, exp_im, exp_re, hw] using neg_exp_one_inv_le_mul_exp

--  this needs annotation
private theorem im_eq_zero_of_arg_add_im_eq_pi_of_mul_exp_mem {w : ℂ}
    (hw1 : w.arg + w.im = π) (hw2 : w * cexp w ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    w.im = 0 := by
  obtain ⟨hzge, hzlt⟩ := mem_Ico.mp <| mem_reProdIm.mp hw2 |>.left
  have hw₀ : w ≠ 0 := fun hw => by simp [hw] at hzlt
  by_contra nh
  obtain ⟨nh, harg⟩ : 0 < w.im ∧ w.arg = π - w.im := by grind [arg_le_pi w]
  have hnormsin : ‖w‖ * Real.sin w.im = w.im := by simpa [harg] using norm_mul_sin_arg w
  have hsin : 0 < Real.sin w.im := by nlinarith [hnormsin, norm_pos_iff.mpr hw₀]
  have hnorm : ‖w‖ = w.im / Real.sin w.im := by rwa [eq_div_iff hsin.ne']
  have hcos : ‖w‖ * -Real.cos w.im = w.re := by simpa [harg] using norm_mul_cos_arg w
  have himpi : w.im < π := by
    by_contra hc
    have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (x := w.im - 2 * π)
      (by linarith [neg_pi_lt_arg w]) (by linarith [not_lt.mp hc])
    grind [Real.sin_sub_two_pi]
  have hbc : w.im * Real.cos w.im < Real.sin w.im := by
    rcases lt_or_ge w.im (π / 2) with h | h
    · have hc : 0 < Real.cos w.im := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h⟩
      simpa [Real.tan_eq_sin_div_cos, hc.ne'] using mul_lt_mul_of_pos_right (Real.lt_tan nh h) hc
    · nlinarith [Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith [himpi]), hsin]
  have hcore : -1 < (w + log w).re := by
    rw [add_re, log_re]
    grind [(div_lt_one hsin).mpr hbc,
      Real.log_pos (show 1 < ‖w‖ by simpa [hnorm, one_lt_div hsin] using Real.sin_lt nh)]
  rw [mul_exp_eq_of_arg_add_im_eq (i := 0) hw₀ (by grind), neg_re, ofReal_re,
    ← Real.exp_neg] at hzge
  linarith [Real.exp_le_exp.mp <| neg_le_neg_iff.mp hzge]

private theorem im_eq_zero_of_arg_add_im_eq_neg_pi_of_mul_exp_mem {w : ℂ}
    (hw1 : w.arg + w.im = -π) (hw2 : w * cexp w ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    w.im = 0 := by
  rw [← neg_eq_zero, ← conj_im]
  apply im_eq_zero_of_arg_add_im_eq_pi_of_mul_exp_mem ?_ ?_
  · rw [conj_im, arg_conj, ite_eq_right (by grind [pi_pos, arg_eq_pi_iff]), ← neg_add, hw1, neg_neg]
  · simp_all [mem_reProdIm, exp_conj, ← map_mul]

private theorem continuousOn_arg_add_im : ContinuousOn (fun w => w.arg + w.im) Complex.slitPlane :=
  continuousOn_arg.add continuous_im.continuousOn

end Complex

section Solve

open Real Complex ComplexConjugate Set Filter Topology

variable {ρ θ : ℝ}

namespace Real

def LambertW.solutionArgAux (θ : ℝ) : ℝ -> ℝ := fun ϕ => (θ - ϕ) / sin ϕ

def LambertW.solutionNormAux (θ : ℝ) : ℝ -> ℝ := fun ϕ =>
  solutionArgAux θ ϕ * rexp (solutionArgAux θ ϕ * cos ϕ)

theorem LambertW.continuousOn_solutionArgAux {s : Set ℝ} (hs : ∀ x ∈ s, sin x ≠ 0) :
    ContinuousOn (solutionArgAux θ) s :=
  continuous_const.sub continuous_id |>.continuousOn |>.div continuous_sin.continuousOn hs

theorem LambertW.continuousOn_solutionNormAux {s : Set ℝ} (hs : ∀ x ∈ s, sin x ≠ 0) :
    ContinuousOn (solutionNormAux θ) s :=
  letI h1 := continuousOn_solutionArgAux hs
  h1.mul (h1.mul continuous_cos.continuousOn).rexp

theorem LambertW.hasDerivAt_solutionArgAux {ϕ : ℝ} (hs : sin ϕ ≠ 0) :
    HasDerivAt (solutionArgAux θ) (-(sin ϕ + (θ - ϕ) * cos ϕ) / sin ϕ ^ 2) ϕ := by
  have hfun : solutionArgAux θ = (fun x : ℝ => θ - x) / sin := rfl
  have h : HasDerivAt ((fun x : ℝ => θ - x) / sin)
      (-(sin ϕ + (θ - ϕ) * cos ϕ) / sin ϕ ^ 2) ϕ := by
    refine ((hasDerivAt_id (x := ϕ)).const_sub θ |>.div (hasDerivAt_sin ϕ) hs).congr_deriv ?_
    simp only [id_eq]
    ring
  rwa [hfun]

theorem LambertW.deriv_solutionArgAux {ϕ : ℝ} (hs : sin ϕ ≠ 0) :
    deriv (solutionArgAux θ) ϕ = -(sin ϕ + (θ - ϕ) * cos ϕ) / sin ϕ ^ 2 :=
  (hasDerivAt_solutionArgAux (θ := θ) hs).deriv

theorem LambertW.deriv_solutionNormAux_neg {ϕ : ℝ} (hϕ : ϕ ∈ Ioo 0 (θ ⊓ π)) :
    deriv (solutionNormAux θ) ϕ < 0 := by
  sorry

theorem LambertW.strictAntiOn_solutionNormAux :
    StrictAntiOn (solutionNormAux θ) (Ioo 0 (θ ⊓ π)) := by
  sorry

theorem LambertW.injOn_solutionNormAux : InjOn (solutionNormAux θ) (Ioo 0 (θ ⊓ π)) :=
  strictAntiOn_solutionNormAux.injOn

theorem LambertW.tendsto_solutionArgAux_nhdsGT_zero (hθ : 0 < θ) :
    Tendsto (solutionArgAux θ) (𝓝[>] 0) atTop := by
  sorry

theorem LambertW.tendsto_solutionNormAux_nhdsGT_zero (hθ : 0 < θ) :
    Tendsto (solutionNormAux θ) (𝓝[>] 0) atTop := by
  sorry

theorem LambertW.tendsto_solutionArgAux_nhdsLT_pi (hθ : π < θ) :
    Tendsto (solutionArgAux θ) (𝓝[<] π) atTop := by
  sorry

theorem LambertW.tendsto_solutionNormAux_nhdsLT_pi (hθ : π < θ) :
    Tendsto (solutionNormAux θ) (𝓝[<] π) (𝓝 0) := by
  sorry

theorem LambertW.tendsto_solutionArgAux_pi_nhdsLT_pi :
    Tendsto (solutionArgAux π) (𝓝[<] π) (𝓝 1) := by
  sorry

theorem LambertW.tendsto_solutionNormAux_pi_nhdsLT_pi :
    Tendsto (solutionNormAux π) (𝓝[<] π) (𝓝 (rexp (-1))) := by
  sorry

theorem LambertW.existsUnique_solutionNormAux_pi (hρ : (rexp 1)⁻¹ < ρ) :
    ∃! φ ∈ Ioo 0 π, solutionNormAux π φ = ρ := by
  sorry

theorem LambertW.existsUnique_solutionNormAux (hθ1 : θ ≠ π) (hθ2 : 0 < θ) (hρ : 0 < ρ) :
    ∃! φ ∈ Ioo 0 (θ ⊓ π), solutionNormAux θ φ = ρ := by
  sorry

private theorem LambertW.existsUnique_mem_Ioo_pi (hρ : (rexp 1)⁻¹ < ρ) :
    ∃! φ ∈ Ioo 0 π, (π - φ) / sin φ * rexp ((π - φ) / sin φ * cos φ) = ρ := by
  simpa only [solutionNormAux, solutionArgAux] using existsUnique_solutionNormAux_pi hρ

--  this needs annotations
private theorem LambertW.existsUnique_mem_Ioo (hθ1 : θ ≠ π) (hθ2 : 0 < θ) (hρ : 0 < ρ) :
    ∃! ϕ ∈ Ioo 0 (θ ⊓ π),
      (θ - ϕ) / sin ϕ * rexp ((θ - ϕ) / sin ϕ * cos ϕ) = ρ := by
  simpa only [solutionNormAux, solutionArgAux] using existsUnique_solutionNormAux hθ1 hθ2 hρ

end Real

namespace Complex

--  this needs annotations
private theorem LambertW.existsUnique_arg_add_im_eq_of_pos (hθ1 : θ ≠ π) (hθ2 : 0 < θ)
    (hρ : 0 < ρ) : ∃! w : ℂ, w.arg + w.im = θ ∧ w * cexp w = ρ * cexp (θ * I) := by
  set r : ℝ -> ℝ := fun ϕ => (θ - ϕ) / ϕ.sin
  obtain ⟨ϕ, ⟨hϕ, hrρ⟩, H⟩ := Real.LambertW.existsUnique_mem_Ioo hθ1 hθ2 hρ
  change r ϕ * rexp (r ϕ * ϕ.cos) = ρ at hrρ
  have hsϕ : 0 < ϕ.sin :=
    Real.sin_pos_of_pos_of_lt_pi hϕ.left <| hϕ.right.trans_le <| min_le_right θ π
  have hr : 0 < r ϕ := by
    unfold r
    refine div_pos_iff_of_pos_left ?_ |>.mpr hsϕ
    simpa using hϕ.right.trans_le <| min_le_left θ π
  refine ⟨r ϕ * cexp (ϕ * I), ⟨?_, ?_⟩, ?_⟩
  · rw [exp_ofReal_mul_I, ofReal_cos, ofReal_sin, arg_mul_cos_add_sin_mul_I hr (by grind)]
    simp [sin_ofReal_re]
    grind
  · calc
      _ = ↑(r ϕ * rexp (r ϕ * ϕ.cos)) * cexp (↑(ϕ + r ϕ * ϕ.sin) * I) := by
        nth_rw 2 [exp_mul_I]
        rw [mul_add, exp_add, ofReal_add, add_mul, exp_add]
        simp
        ring_nf
      _ = ρ * cexp (θ * I) := by grind
  · intro w' ⟨hw'ϕ, hw'ρ⟩
    have hw'ϕ_ne_pi : w'.arg ≠ π := by grind [arg_add_im_eq_pi_of_arg_eq_pi]
    have hw'₀ : w' ≠ 0 := fun nh =>
      mul_ne_zero (ofReal_ne_zero.mpr hρ.ne') (exp_ne_zero _) <| by rw [← hw'ρ, nh, zero_mul]
    have hθ'2 : 0 < w'.arg + w'.im := hw'ϕ ▸ hθ2
    have hw'r : ‖w'‖ = r (w'.arg) := by
      grind [eq_div_iff <| sin_arg_ne_zero_of_arg_add_im_pos hw'₀ hw'ϕ_ne_pi hθ'2, norm_mul_sin_arg]
    have hρ' : r (w'.arg) * rexp (r (w'.arg) * Real.cos w'.arg) = ρ := by
      have hc : ‖w' * cexp w'‖ = ‖ρ * cexp (θ * I)‖ := congrArg norm hw'ρ
      rw [norm_mul, norm_exp, ← norm_mul_cos_arg, hw'r] at hc
      simpa [norm_exp, norm_real, abs_of_pos hρ] using hc
    calc
      w' = ‖w'‖ * cexp (w'.arg * I) := norm_mul_exp_arg_mul_I w' |>.symm
      _ = (r (w'.arg)) * cexp (w'.arg * I) := by rw [hw'r]
      _ = (r ϕ) * cexp (ϕ * I) := by
        rw [H w'.arg ⟨hw'ϕ ▸ arg_mem_Ioo_of_arg_add_im_pos hw'₀ hw'ϕ_ne_pi hθ'2, hρ'⟩]

private theorem LambertW.existsUnique_arg_add_im_eq_pi (hρ : (rexp 1)⁻¹ < ρ) :
    ∃! w : ℂ, w.arg + w.im = π ∧ w * cexp w = ρ * cexp (π * I) ∧ w.im > 0 := by
  have hρ0 : 0 < ρ := (inv_pos.mpr (Real.exp_pos 1)).trans hρ
  set r : ℝ → ℝ := fun ϕ => (π - ϕ) / ϕ.sin with hrdef
  obtain ⟨ϕ, ⟨hϕ, hrρ⟩, H⟩ := Real.LambertW.existsUnique_mem_Ioo_pi hρ
  change r ϕ * rexp (r ϕ * ϕ.cos) = ρ at hrρ
  have hsϕ : 0 < ϕ.sin := sin_pos_of_pos_of_lt_pi hϕ.1 hϕ.2
  have hr : 0 < r ϕ := div_pos (sub_pos.mpr hϕ.2) hsϕ
  have hrsin : r ϕ * ϕ.sin = π - ϕ := by rw [hrdef]; exact div_mul_cancel₀ _ hsϕ.ne'
  have himr : ∀ ψ : ℝ, (r ψ * cexp (ψ * I)).im = r ψ * Real.sin ψ := fun ψ => by
    have h : (↑(r ψ) * (↑(Real.cos ψ) + ↑(Real.sin ψ) * I) : ℂ)
        = ↑(r ψ * Real.cos ψ) + ↑(r ψ * Real.sin ψ) * I := by push_cast; ring
    rw [exp_ofReal_mul_I, h, add_im, ofReal_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  refine ⟨r ϕ * cexp (ϕ * I), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [himr, exp_ofReal_mul_I, ofReal_cos, ofReal_sin,
      arg_mul_cos_add_sin_mul_I hr ⟨by grind [Real.pi_pos, hϕ.left], hϕ.right.le⟩,
      hrsin, add_sub_cancel]
  · calc (r ϕ * cexp (ϕ * I)) * cexp (r ϕ * cexp (ϕ * I))
        = (r ϕ * cexp (ϕ * I)) * (cexp (↑(r ϕ * ϕ.cos)) * cexp (↑(r ϕ * ϕ.sin) * I)) := by
          nth_rw 2 [exp_ofReal_mul_I]
          rw [mul_add, exp_add]
          push_cast
          ring_nf
      _ = (r ϕ * rexp (r ϕ * ϕ.cos)) * (cexp (ϕ * I) * cexp (↑(r ϕ * ϕ.sin) * I)) := by
          rw [ofReal_exp]
          ring
      _ = (r ϕ * rexp (r ϕ * ϕ.cos)) * cexp ((ϕ * I) + (↑(r ϕ * ϕ.sin) * I)) := by rw [exp_add]
      _ = (r ϕ * rexp (r ϕ * ϕ.cos)) * cexp ((ϕ + r ϕ * ϕ.sin) * I) := by
          push_cast
          ring_nf
      _ = ρ * cexp (π * I) := by
          rw [← ofReal_mul, hrρ, ← ofReal_mul, ← ofReal_add, hrsin, add_sub_cancel]
  · rw [himr, hrsin, gt_iff_lt, sub_pos]
    exact hϕ.right
  · intro w' ⟨hw'ϕ, hw'ρ, hw'im⟩
    have hw'arg_ne : w'.arg ≠ π := fun h => by grind [arg_eq_pi_iff]
    have hθ'2 : 0 < w'.arg + w'.im := by grw [hw'ϕ, pi_pos]
    have hw'arg0 : 0 < w'.arg := arg_pos_of_arg_add_im_pos hθ'2
    have hw'argπ : w'.arg < π := by grind
    have hw'₀ : w' ≠ 0 := fun nh =>
      (mul_ne_zero (ofReal_ne_zero.mpr hρ0.ne') (exp_ne_zero _)) (by rw [← hw'ρ, nh]; simp)
    have hw'r : ‖w'‖ = r (w'.arg) := by
      have h : ‖w'‖ * Real.sin w'.arg = π - w'.arg := by
        rw [norm_mul_sin_arg, ← hw'ϕ, eq_sub_iff_add_eq']
      rw [hrdef, eq_div_iff (sin_arg_ne_zero_of_arg_add_im_pos hw'₀ hw'arg_ne hθ'2)]
      linarith
    have hρ' : r (w'.arg) * rexp (r (w'.arg) * Real.cos w'.arg) = ρ := by
      have hc : ‖w' * cexp w'‖ = ‖ρ * cexp (π * I)‖ := congrArg norm hw'ρ
      rw [norm_mul, norm_exp, norm_mul, norm_exp, ← norm_mul_cos_arg, hw'r] at hc
      simpa [abs_of_pos hρ0] using hc
    calc w' = ‖w'‖ * cexp (w'.arg * I) := (norm_mul_exp_arg_mul_I w').symm
      _ = r (w'.arg) * cexp (w'.arg * I) := by rw [hw'r]
      _ = r ϕ * cexp (ϕ * I) := by rw [H w'.arg ⟨⟨hw'arg0, hw'argπ⟩, hρ'⟩]

private theorem LambertW.existsUnique_arg_add_im_eq (hθ1 : θ ≠ π) (hθ2 : θ ≠ -π) (hρ : 0 < ρ) :
    ∃! w : ℂ, w.arg + w.im = θ ∧ w * cexp w = ρ * cexp (θ * I) := by
  rcases lt_trichotomy θ 0 with hθ' | rfl | hθ'
  · obtain ⟨w, ⟨hw1, hw2⟩, H⟩ : ∃! w : ℂ, w.arg + w.im = -θ ∧ w * cexp w = ρ * cexp (↑(-θ) * I) :=
      LambertW.existsUnique_arg_add_im_eq_of_pos (θ := -θ) (by grind) (by linarith) hρ
    refine ⟨conj w, ⟨?_, ?_⟩, ?_⟩
    · simp [arg_conj, show w.arg ≠ π by grind [arg_eq_pi_iff], ← neg_add, hw1]
    · rw [exp_conj, ← map_mul, hw2, map_mul, conj_ofReal,
        ← exp_conj, map_mul, conj_I, conj_ofReal, ofReal_neg, neg_mul_neg]
    · intro w' ⟨hw'ϕ, hw'ρ⟩
      have hw'ϕ1 : w'.arg ≠ π := by grind [arg_add_im_eq_pi_of_arg_eq_pi]
      specialize H (conj w') ⟨?_, ?_⟩
      · simp [arg_conj, hw'ϕ1, ← hw'ϕ, add_comm]
      · simp [← map_mul, hw'ρ]
        simp [← exp_conj, conj_ofReal, conj_I]
      rw [← H, conj_conj]
  · rw [ofReal_zero, zero_mul, exp_zero, mul_one]
    obtain ⟨x, hx, H⟩ := existsUnique_add_log_eq (Real.log ρ)
    refine ⟨x, ⟨?_, ?_⟩, ?_⟩
    · simp [arg_eq_zero_iff, hx.left.le]
    · apply Complex.ext
      · simp only [mul_re, ofReal_re, ofReal_im, exp_ofReal_im, mul_zero, sub_zero, exp_ofReal_re]
        rw [← Real.exp_log hρ, ← hx.right, Real.exp_add, Real.exp_log hx.left, mul_comm]
      · simp
    · intro x' ⟨hx'1, hx'2⟩
      have him : x'.im = 0 := im_eq_zero_of_arg_add_im_eq_zero hx'1
      have harg : x'.arg = 0 := by grind
      rw [Complex.ext (z := x') (w := x'.re) rfl him] at hx'2 ⊢
      replace hx'2 := congrArg re hx'2
      simp only [mul_re, ofReal_re, exp_ofReal_re, ofReal_im, exp_ofReal_im, mul_zero,
        sub_zero] at hx'2
      have : 0 < x'.re := by grind [arg_eq_zero_iff]
      replace hx'2 := congrArg Real.log hx'2
      rw [Real.log_mul this.ne' (Real.exp_ne_zero x'.re), Real.log_exp, add_comm] at hx'2
      specialize H x'.re ⟨this, hx'2⟩
      rw [← H]
  · exact LambertW.existsUnique_arg_add_im_eq_of_pos hθ1 hθ' hρ

end Complex

end Solve

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

-- /-- TODO doc -/
-- def LambertW.openBranchCut (k : ℤ) : Set ℂ :=
--   Iio (if k = 0 then -(rexp 1)⁻¹ else 0) ×ℂ {0}

/-- TODO doc -/
def LambertW.slitPlane (k : ℤ) : Set ℂ :=
  (branchCut k)ᶜ

-- /-- TODO doc, ref this? https://en.wikipedia.org/wiki/Quadratrix_of_Hippias -/
-- def LambertW.boundaryAux (k : ℤ) : Set ℂ :=
--   { w | w.arg + w.im = (2 * k + 1) * π }
  -- (fun t => ⟨-t * Real.cot t, t⟩) '' Ioo (k * π) ((k + 1) * π)

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
def LambertW.openRange (k : ℤ) : Set ℂ :=
  if k = 0 then {w | w.arg + w.im ∈ Ioo (-π) π} ∪ Ioo (-1) 0 ×ℂ {0} else
    {w | w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π)}
  -- {w | LambertW.StrictAboveBoundary k w ∧ LambertW.StrictBelowBondary k w}

@[simp]
theorem LambertW.openRange_zero :
    openRange 0 = {w | w.arg + w.im ∈ Ioo (-π) π} ∪ Ioo (-1) 0 ×ℂ {0} :=
  rfl

theorem LambertW.openRange_of_ne_zero (hk : k ≠ 0) :
    openRange k = {w | w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π)} :=
  ite_eq_right hk

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

theorem LambertW.ne_zero_of_mem_range (hk : k ≠ 0) (hz : z ∈ range k) : z ≠ 0 := fun nh =>
  False.elim <| zero_notMem_range hk <| nh ▸ hz

@[simp]
theorem LambertW.zero_mem_range_iff : 0 ∈ range k ↔ k = 0 := by
  grind [zero_notMem_range, zero_mem_range_zero]

@[simp]
theorem LambertW.neg_one_mem_range_neg_one : -1 ∈ range (-1) := by
  simp [mem_range_neg_one_iff]

@[simp]
theorem LambertW.neg_one_mem_range_zero : -1 ∈ range 0 := by
  simp [mem_range_zero_iff, pi_pos]

theorem LambertW.arg_of_mem (hw : w ∈ Iic (-1) ×ℂ {0}) : w.arg = π :=
  arg_eq_pi_iff.mpr ⟨hw.left.trans_lt neg_one_lt_zero, hw.right⟩

theorem LambertW.arg_add_im_of_mem (hw : w ∈ Iic (-1) ×ℂ {0}) : w.arg + w.im = π :=
  arg_add_im_eq_pi_of_arg_eq_pi (arg_of_mem hw)

theorem LambertW.mem_range_iff_of_mem (hw : w ∈ Iic (-1) ×ℂ {0}) :
    w ∈ range k ↔ k = -1 ∨ (k = 0 ∧ w.re = -1) := by
  simp only [mem_reProdIm, mem_Iic, mem_singleton_iff] at hw
  constructor
  · intro h
    rcases (show k = 0 ∨ k = -1 ∨ (k ≠ 0 ∧ k ≠ -1) by tauto) with rfl | rfl | ⟨hk, hk'⟩
    · refine Or.inr ⟨rfl, le_antisymm hw.left ?_⟩
      by_contra nh
      exact mem_range_zero_iff.mp h |>.right ⟨not_le.mp nh, hw.right⟩
    · exact Or.inl rfl
    · rw [mem_range_iff_of_ne hk hk', arg_add_im_of_mem hw] at h
      simp [field] at h
      norm_cast at h
      omega
  · rintro (rfl | ⟨rfl, hre⟩)
    · exact mem_range_neg_one_iff.mpr (Or.inr ⟨hw.1, hw.2⟩)
    · apply mem_range_zero_iff.mpr
      grind [arg_add_im_of_mem hw, pi_pos]

theorem LambertW.mem_range_iff_of_notMem (hw : w ∉ Iic (-1) ×ℂ {0}) :
    w ∈ range k ↔ w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) := by
  rcases (show k = 0 ∨ k = -1 ∨ (k ≠ 0 ∧ k ≠ -1) by tauto) with rfl | rfl | ⟨hk, hk'⟩
  · rw [mem_range_zero_iff]
    have : ¬(w.re < -1 ∧ w.im = 0) := fun ⟨hre, him⟩ => hw ⟨hre.le, him⟩
    simp [this]
  · rw [mem_range_neg_one_iff]
    have : ¬(w.re ≤ -1 ∧ w.im = 0) := hw
    simp [this]
    grind
  · exact mem_range_iff_of_ne hk hk'

theorem LambertW.mem_openRange_zero_iff :
    w ∈ openRange 0 ↔ w.arg + w.im ∈ Ioo (-π) π ∨ (w.re ∈ Ioo (-1) 0 ∧ w.im = 0) := by
  simp [openRange_zero, mem_reProdIm]

theorem LambertW.mem_openRange_iff_of_ne (hk : k ≠ 0) :
    w ∈ openRange k ↔ w.arg + w.im ∈ Ioo ((2 * (k : ℝ) - 1) * π) ((2 * (k : ℝ) + 1) * π) := by
  simp [openRange_of_ne_zero hk]

private theorem LambertW.existsUnique_eq_pi_mul_exp_eq (hz : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0}) :
    ∃! w : ℂ, w.arg + w.im = π ∧ w * cexp w = z ∧ w.im > 0 := by
  set θ := π with hθ
  set ρ := ‖z‖
  have hz₀ : z ≠ 0 := fun nh => by simp [nh, mem_reProdIm, Real.exp_pos 1 |>.not_gt] at hz
  have hρ : (rexp 1)⁻¹ < ‖z‖ := by
    rw [norm_eq_sqrt_sq_add_sq, hz.right, zero_pow (by omega), add_zero, sqrt_sq_eq_abs,
      abs_of_neg, lt_neg]
    · exact hz.left
    · apply hz.left.trans
      simp [exp_pos]
  have hargz : z.arg = π := arg_eq_pi_iff.mpr ⟨hz.left.trans (by simp [Real.exp_pos]), hz.right⟩
  have hθz : cexp (θ * I) = cexp (z.arg * I) := by rw [hargz]
  have hz' : z = ρ * cexp (θ * I) := by rw [← norm_mul_exp_arg_mul_I z, hθz]
  obtain ⟨w, ⟨hw, hwz⟩, H⟩ := LambertW.existsUnique_arg_add_im_eq_pi hρ
  refine ⟨w, ⟨hw, hz' ▸ hwz⟩, ?_⟩
  intro w' ⟨hw', hw'z, hw'im⟩
  refine H w' ⟨?_, ?_, hw'im⟩
  · have hw'₀ : w' ≠ 0 := by grind
    nth_rw 1 [← exp_log hz₀, ← exp_log hw'₀, ← exp_add, add_comm] at hw'z
    rw [exp_eq_exp_iff_exists_int] at hw'z
    obtain ⟨k', hk'⟩ := hw'z
    apply congrArg im at hk'
    rw [add_im, log_im, add_im, log_im, add_comm] at hk'
    simp only [mul_im, intCast_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
      sub_zero, I_im, mul_one, zero_mul, add_zero, I_re, intCast_im, sub_self] at hk'
    suffices k' = 0 by grind
    rw [hk', hargz] at hw'
    clear * - hw'
    simpa [θ] using hw'
  · rw [← norm_mul_exp_arg_mul_I z] at hw'z
    rw [hw'z, hθz]

private theorem LambertW.existsUnique_mem_Ico_exp_eq (hz : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    ∃! w : ℂ, w ∈ Ico (-1) 0 ×ℂ {0} ∧ w * cexp w = z := by
  obtain ⟨x, ⟨hx1, hx2⟩, H⟩ := existsUnique_mem_Ico_mul_exp_eq_of_mem_Ico hz.left
  refine ⟨x, ⟨by simpa [mem_reProdIm], ?_⟩, ?_⟩
  · simpa [Complex.ext_iff, exp_re, hx2] using hz.right.symm
  · intro w' ⟨hw'1, hw'2⟩
    apply Complex.ext (z := w') (w := x) (H w'.re ⟨hw'1.left, ?_⟩) hw'1.right
    simp [← hw'2, exp_re, mem_singleton_iff.mp <| mem_reProdIm.mp hw'1 |>.right]

private theorem LambertW.existsUnique_mem_Iic_exp_eq (hz : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    ∃! w : ℂ, w ∈ Iic (-1) ×ℂ {0} ∧ w * cexp w = z := by
  obtain ⟨x, ⟨hx1, hx2⟩, H⟩ := existsUnique_mem_Iic_mul_exp_eq_of_mem_Ico hz.left
  refine ⟨x, ⟨by simpa [mem_reProdIm], ?_⟩, ?_⟩
  · simpa [Complex.ext_iff, exp_re, hx2] using hz.right.symm
  · intro w' ⟨hw'1, hw'2⟩
    apply Complex.ext (z := w') (w := x) (H w'.re ⟨hw'1.left, ?_⟩) hw'1.right
    simp [← hw'2, exp_re, mem_singleton_iff.mp <| mem_reProdIm.mp hw'1 |>.right]

private theorem LambertW.existsUnique_eq_neg_pi_mul_exp_eq (hz : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0}) :
    ∃! w : ℂ, w.arg + w.im = -π ∧ w * cexp w = z := by
  obtain ⟨w, ⟨hw, hwz, hwim⟩, H⟩ := LambertW.existsUnique_eq_pi_mul_exp_eq hz
  refine ⟨conj w, ⟨?_, ?_⟩, ?_⟩
  · rw [arg_conj, conj_im, ite_eq_right, ← hw, neg_add]
    grind
  · rw [exp_conj, ← map_mul, hwz, conj_eq_iff_im, hz.right]
  · intro w' ⟨hw', hw'z⟩
    rw [← H (conj w') ⟨?_, ?_, ?_⟩, conj_conj]
    · rw [arg_conj, conj_im, ite_eq_right, ← neg_add, hw', neg_neg]
      grind [pi_pos, arg_eq_pi_iff]
    · rw [exp_conj, ← map_mul, hw'z, conj_eq_iff_im, hz.right]
    · grind [arg_mem_Ioc w', pi_pos, conj_im]

private theorem LambertW.existsUnique_eq_mul_exp_eq
    (hk : k ≠ 0) (hk' : k ≠ -1) (hz : z ∈ Iio 0 ×ℂ {0}) :
    ∃! w : ℂ, w.arg + w.im = (2 * k + 1) * π ∧ w * cexp w = z := by
  set θ := (2 * k + 1) * π with hθ
  set ρ := ‖z‖
  have hz₀ : z ≠ 0 := fun nh => by simp [nh, mem_reProdIm] at hz
  have hargz : z.arg = π := arg_eq_pi_iff.mpr ⟨hz.left, hz.right⟩
  have hθz : cexp (θ * I) = cexp (z.arg * I) := by
    rw [hθ, hargz, ofReal_mul, ofReal_add, add_mul, add_mul, add_comm, ofReal_mul, ofReal_intCast,
      ofReal_ofNat, mul_comm 2, mul_assoc (k * 2 : ℂ), mul_assoc (k : ℂ), ← mul_assoc 2,
      exp_periodic.int_mul k, ofReal_one, one_mul]
  have hz' : z = ρ * cexp (θ * I) := by rw [← norm_mul_exp_arg_mul_I z, hθz]
  have hθ1 : θ ≠ π := by
    rcases (show k ≤ -2 ∨ k ≥ 1 by omega) with hk | hk <;> [apply ne_of_lt; apply ne_of_gt]
      <;> grw [hθ, hk] <;> grind [pi_pos]
  have hθ2 : θ ≠ -π := by
    rcases (show k ≤ -2 ∨ k ≥ 1 by omega) with hk | hk <;> [apply ne_of_lt; apply ne_of_gt]
      <;> grw [hθ, hk] <;> grind [pi_pos]
  obtain ⟨w, ⟨hw, hwz⟩, H⟩ := LambertW.existsUnique_arg_add_im_eq hθ1 hθ2 <| norm_pos_iff.mpr hz₀
  refine ⟨w, ⟨hw, hz' ▸ hwz⟩, ?_⟩
  intro w' ⟨hw', hw'z⟩
  refine H w' ⟨?_, ?_⟩
  · have hw'₀ : w' ≠ 0 := by grind
    nth_rw 1 [← exp_log hz₀, ← exp_log hw'₀, ← exp_add, add_comm]  at hw'z
    rw [exp_eq_exp_iff_exists_int] at hw'z
    obtain ⟨k', hk'⟩ := hw'z
    apply congrArg im at hk'
    rw [add_im, log_im, add_im, log_im, add_comm] at hk'
    simp only [mul_im, intCast_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
      sub_zero, I_im, mul_one, zero_mul, add_zero, I_re, intCast_im, sub_self] at hk'
    suffices k' = k by grind
    rw [hk', hargz] at hw'
    clear * - hw'
    rcases lt_trichotomy k' k with nh | rfl | nh
    · nlinarith [show 1 ≤ (k : ℝ) - (k' : ℝ) from mod_cast by omega, pi_pos]
    · rfl
    · nlinarith [show 1 ≤ (k' : ℝ) - (k : ℝ) from mod_cast by omega, pi_pos]
  · rw [← norm_mul_exp_arg_mul_I z] at hw'z
    rw [hw'z, hθz]

private theorem LambertW.existsUnique_mem_Ioo_mul_exp_eq (k : ℤ) (hz : z ∈ Complex.slitPlane) :
    ∃! w : ℂ, w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π) ∧ w * cexp w = z := by
  set θ := z.arg + k * (2 * π) with hθ
  set ρ := ‖z‖
  have hθz : cexp (θ * I) = cexp (z.arg * I) := by
    rw [hθ, ofReal_add, add_mul, ofReal_mul, ofReal_intCast, ofReal_mul, ofReal_ofNat,
      mul_assoc, exp_periodic.int_mul k]
  have hz' : z = ρ * cexp (θ * I) := by
    rw [← norm_mul_exp_arg_mul_I z, hθz]
  have hθ' : z.arg ∈ Ioo (-π) π :=
    ⟨arg_mem_Ioc z |>.left, lt_of_le_of_ne (arg_mem_Ioc z |>.right) <| slitPlane_arg_ne_pi hz⟩
  have hθ1 : θ ≠ π := by
    rcases (show k ≤ 0 ∨ k ≥ 1 by omega) with hk | hk <;> [apply ne_of_lt; apply ne_of_gt]
      <;> grw [hθ, hk] <;> grind
  have hθ2 : θ ≠ -π := by
    rcases (show k ≤ -1 ∨ k ≥ 0 by omega) with hk | hk <;> [apply ne_of_lt; apply ne_of_gt]
      <;> grw [hθ, hk] <;> grind
  obtain ⟨w, ⟨hw, hwz⟩, H⟩ := LambertW.existsUnique_arg_add_im_eq hθ1 hθ2
    (norm_pos_iff.mpr <| slitPlane_ne_zero hz)
  refine ⟨w, by grind, ?_⟩
  intro w' ⟨hw', hw'z⟩
  refine H w' ⟨?_, ?_⟩
  · have hz₀ : z ≠ 0 := slitPlane_ne_zero hz
    have hw'₀ : w' ≠ 0 := by grind
    nth_rw 1 [← exp_log hz₀, ← exp_log hw'₀, ← exp_add, add_comm]  at hw'z
    rw [exp_eq_exp_iff_exists_int] at hw'z
    obtain ⟨k', hk'⟩ := hw'z
    apply congrArg im at hk'
    rw [add_im, log_im, add_im, log_im, add_comm] at hk'
    simp only [mul_im, intCast_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
      sub_zero, I_im, mul_one, zero_mul, add_zero, I_re, intCast_im, sub_self] at hk'
    suffices k' = k by grind
    rw [hk', add_mem_Ioo_iff_left] at hw'
    clear * - hw' hθ'
    simp only [mem_Ioo] at hθ' hw'
    rcases lt_trichotomy k' k with nh | rfl | nh
    · nlinarith [show 1 ≤ (k : ℝ) - (k' : ℝ) from mod_cast by omega]
    · rfl
    · nlinarith [show 1 ≤ (k' : ℝ) - (k : ℝ) from mod_cast by omega]
  · rw [← norm_mul_exp_arg_mul_I z] at hw'z
    rw [hw'z, hθz]

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
  rcases lt_or_ge z.re (-(rexp 1)⁻¹) with hz'' | hz''
  · replace hz'' : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, ⟨hwl, hwz, hwr⟩, -⟩ := existsUnique_eq_pi_mul_exp_eq hz''
    simp only [mem_image, mem_range_zero_iff, mem_Ioc, not_and]
    use w, ⟨⟨by rw [hwl]; linarith [pi_pos], hwl.le⟩, by simp [hwr.ne']⟩, hwz
  · replace hz'' : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, ⟨hw, hwz⟩, -⟩ := LambertW.existsUnique_mem_Ico_exp_eq hz''
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
  rcases le_or_gt (-(rexp 1)⁻¹) z.re with hz'' | hz''
  · replace hz : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, ⟨hw, hwz⟩, -⟩ := existsUnique_mem_Iic_exp_eq hz
    simp only [Int.reduceNeg, mem_image, mem_range_neg_one_iff, neg_mul, mem_Ioc]
    simp only [mem_reProdIm, mem_singleton_iff] at hw
    use w, Or.inr ⟨hw.left, hw.right⟩, hwz
  · replace hz : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, ⟨hw, hwz⟩, -⟩ := existsUnique_eq_neg_pi_mul_exp_eq hz
    simp only [Int.reduceNeg, mem_image, mem_range_neg_one_iff, neg_mul, mem_Ioc]
    use w, Or.inl ⟨by rw [hw]; linarith [pi_pos], hw.le⟩, hwz

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
  by_cases hk' : k = -1
  · rw [hk', image_mul_exp_range_neg_one, domain_of_ne_zero (by simp)]
  · rw [image_mul_exp_range_of_ne_zero hk hk', domain_of_ne_zero hk]

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
  rename z = w₂ * cexp w₂ => hz₂
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
      apply lt_of_le_of_ne hw₁.left.right
      intro nh
      obtain ⟨k, hk⟩ := arg_add_im_eq_arg_add_of_eq (slitPlane_ne_zero hz) hz₁.symm
      rw [hk] at nh
      have hz'' := arg_mem_Ioc z
      obtain rfl : k = 0 := by
        rcases (show k ≤ -1 ∨ k = 0 ∨ k ≥ 1 by omega) with hk | rfl | hk
        · nlinarith [show k ≤ (-1 : ℝ) from mod_cast hk, pi_pos, hz''.right]
        · rfl
        · nlinarith [show k ≥ (1 : ℝ) from mod_cast hk, pi_pos, hz''.left]
      simp only [Int.cast_zero, zero_mul, add_zero, arg_eq_pi_iff_lt_zero] at nh
      exact hz' nh
    have hw₂' : w₂.arg + w₂.im < π := by
      apply lt_of_le_of_ne hw₂.left.right
      intro nh
      obtain ⟨k, hk⟩ := arg_add_im_eq_arg_add_of_eq (slitPlane_ne_zero hz) hz₂.symm
      rw [hk] at nh
      have hz'' := arg_mem_Ioc z
      obtain rfl : k = 0 := by
        rcases (show k ≤ -1 ∨ k = 0 ∨ k ≥ 1 by omega) with hk | rfl | hk
        · nlinarith [show k ≤ (-1 : ℝ) from mod_cast hk, pi_pos, hz''.right]
        · rfl
        · nlinarith [show k ≥ (1 : ℝ) from mod_cast hk, pi_pos, hz''.left]
      simp only [Int.cast_zero, zero_mul, add_zero, arg_eq_pi_iff_lt_zero] at nh
      exact hz' nh
    have Hw₁ := hw w₁ ⟨⟨hw₁.left.left, hw₁'⟩, hz₁.symm⟩
    have Hw₂ := hw w₂ ⟨⟨hw₂.left.left, hw₂'⟩, hz₂.symm⟩
    exact Hw₂ ▸ Hw₁
  have hw₁' : w₁.arg + w₁.im = π := by grind [mul_exp_mem_of_arg_add_im_eq (w := w₁) (i := 0)]
  have hw₂' : w₂.arg + w₂.im = π := by grind [mul_exp_mem_of_arg_add_im_eq (w := w₂) (i := 0)]
  rcases lt_or_ge z.re (-(rexp 1)⁻¹) with hz'' | hz''
  · replace hz'' : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, -, hw⟩ := existsUnique_eq_pi_mul_exp_eq hz''
    have hw₁im : w₁.im > 0 := by
      apply lt_of_le_of_ne <| arg_nonneg_iff.mp <| (arg_pos_of_arg_add_im_pos <| hw₁' ▸ pi_pos).le
      intro nh
      rw [← nh, add_zero, arg_eq_pi_iff] at hw₁'
      exact hz''.left.not_ge <| mem_reProdIm.mp (hz₁ ▸ mul_exp_mem_of_im_eq_zero hw₁'.right) |>.left
    have hw₂im : w₂.im > 0 := by
      apply lt_of_le_of_ne <| arg_nonneg_iff.mp <| (arg_pos_of_arg_add_im_pos <| hw₂' ▸ pi_pos).le
      intro nh
      rw [← nh, add_zero, arg_eq_pi_iff] at hw₂'
      exact hz''.left.not_ge <| mem_reProdIm.mp (hz₂ ▸ mul_exp_mem_of_im_eq_zero hw₂'.right) |>.left
    have Hw₁ := hw w₁ ⟨hw₁', rfl, hw₁im⟩
    have Hw₂ := hw w₂ ⟨hw₂', hz₂ ▸ rfl, hw₂im⟩
    exact Hw₂ ▸ Hw₁
  · replace hz'' : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, -, hw⟩ := LambertW.existsUnique_mem_Ico_exp_eq hz''
    replace hw₁ : w₁ ∈ Ico (-1) 0 ×ℂ {0} := by
      suffices w₁.im = 0 by
        rw [this, add_zero, arg_eq_pi_iff] at hw₁'
        refine ⟨⟨?_, hw₁'.left⟩, this⟩
        simpa [hw₁'] using hw₁.right
      exact im_eq_zero_of_arg_add_im_eq_pi_of_mul_exp_mem hw₁' (hz₁ ▸ hz'')
    replace hw₂ : w₂ ∈ Ico (-1) 0 ×ℂ {0} := by
      suffices w₂.im = 0 by
        rw [this, add_zero, arg_eq_pi_iff] at hw₂'
        refine ⟨⟨?_, hw₂'.left⟩, this⟩
        simpa [hw₂'] using hw₂.right
      exact im_eq_zero_of_arg_add_im_eq_pi_of_mul_exp_mem hw₂' (hz₂ ▸ hz'')
    have Hw₁ := hw w₁ ⟨hw₁, hz₁.symm⟩
    have Hw₂ := hw w₂ ⟨hw₂, hz₂.symm⟩
    exact Hw₂ ▸ Hw₁

private theorem LambertW.injOn_mul_exp_range_neg_one :
    InjOn (fun w => w * cexp w) (range (-1)) := by
  intro w₁ hw₁ w₂ hw₂ (h : w₁ * cexp w₁ = w₂ * cexp w₂)
  rw [mem_range_neg_one_iff] at hw₁ hw₂
  set z := w₁ * cexp w₁ with hz₁
  have hz₂ : z = w₂ * cexp w₂ := h ▸ hz₁
  by_cases hz : z = 0
  · simp_all
  by_cases hz' : z ∈ Iio 0 ×ℂ {0}
  case neg =>
    replace hz : z ∈ Complex.slitPlane := by
      simp [Complex.ext_iff, mem_reProdIm, mem_slitPlane_iff] at hz hz' ⊢
      grind
    obtain ⟨w, -, hw⟩ := existsUnique_mem_Ioo_mul_exp_eq (-1) hz
    simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, mul_neg, mul_one, mem_Ioo, fieldLt,
      fieldEq, and_imp] at hw
    replace hw₁ : w₁.arg + w₁.im ∈ Ioc (-3 * π) (-π) := by
      apply Or.resolve_right hw₁ fun nh => hz' ?_
      simp [mem_reProdIm, hz₁, exp_re, exp_im, nh, mul_neg_iff, Real.exp_pos w₁.re, LT.lt.not_gt]
      grind
    replace hw₂ : w₂.arg + w₂.im ∈ Ioc (-3 * π) (-π) := by
      apply Or.resolve_right hw₂ fun nh => hz' ?_
      simp [mem_reProdIm, hz₂, exp_re, exp_im, nh, mul_neg_iff, Real.exp_pos w₂.re, LT.lt.not_gt]
      grind
    replace hw₁ : w₁.arg + w₁.im ∈ Ioo (-3 * π) (-π) := by
      refine ⟨hw₁.left, lt_of_le_of_ne hw₁.right fun nh => ?_⟩
      have := arg_mul_exp_eq_of_mem (x := w₁) (i := -1) (by grind [slitPlane_ne_zero hz]) (by grind)
      rw [nh, ← hz₁] at this
      conv_rhs at this => ring_nf
      rw [arg_eq_pi_iff] at this
      exact hz' this
    replace hw₂ : w₂.arg + w₂.im ∈ Ioo (-3 * π) (-π) := by
      refine ⟨hw₂.left, lt_of_le_of_ne hw₂.right fun nh => ?_⟩
      have := arg_mul_exp_eq_of_mem (x := w₂) (i := -1) (by grind [slitPlane_ne_zero hz]) (by grind)
      rw [nh, ← hz₂] at this
      conv_rhs at this => ring_nf
      rw [arg_eq_pi_iff] at this
      exact hz' this
    have Hw₁ := hw w₁ (by grind) (by grind) rfl
    have Hw₂ := hw w₂ (by grind) (by grind) h.symm
    exact Hw₂ ▸ Hw₁
  rcases lt_or_ge z.re (-(rexp 1)⁻¹) with hz'' | hz''
  · replace hz'' : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, -, hw⟩ := existsUnique_eq_neg_pi_mul_exp_eq hz''
    replace hw₁ := hw₁.resolve_right <| fun nh => by
      absurd hz''.left
      simp [hz₁, exp_im, exp_re, nh, neg_exp_one_inv_le_mul_exp]
    replace hw₂ := hw₂.resolve_right <| fun nh => by
      absurd hz''.left
      simp [hz₂, exp_im, exp_re, nh, neg_exp_one_inv_le_mul_exp]
    have Hw₁ := hw w₁ ⟨by grind [mul_exp_mem_of_arg_add_im_eq (w := w₁) (i := -1)], rfl⟩
    have Hw₂ := hw w₂ ⟨by grind [mul_exp_mem_of_arg_add_im_eq (w := w₂) (i := -1)], hz₂.symm⟩
    exact Hw₂ ▸ Hw₁
  · replace hz'' : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, -, hw⟩ := existsUnique_mem_Iic_exp_eq hz''
    replace hw₁ := hw₁.resolve_left <| fun nh => by
      have := hz₁ ▸ arg_mul_exp_eq_of_mem (x := w₁) (i := -1) (by grind) (by grind)
      rw [arg_eq_pi_iff.mpr hz'] at this
      replace := im_eq_zero_of_arg_add_im_eq_neg_pi_of_mul_exp_mem (by grind) hz''
      grind [arg_mem_Ioc]
    replace hw₂ := hw₂.resolve_left <| fun nh => by
      have := hz₂ ▸ arg_mul_exp_eq_of_mem (x := w₂) (i := -1) (by grind) (by grind)
      rw [arg_eq_pi_iff.mpr hz'] at this
      replace := im_eq_zero_of_arg_add_im_eq_neg_pi_of_mul_exp_mem (by grind) (hz₂ ▸ hz'')
      grind [arg_mem_Ioc]
    have Hw₁ := hw w₁ ⟨hw₁, rfl⟩
    have Hw₂ := hw w₂ ⟨hw₂, hz₂.symm⟩
    exact Hw₂ ▸ Hw₁

private theorem LambertW.injOn_mul_exp_range_of_ne (hk : k ≠ 0) (hk' : k ≠ -1) :
    InjOn (fun w => w * cexp w) (range k) := by
  intro w₁ hw₁ w₂ hw₂ (h : w₁ * cexp w₁ = w₂ * cexp w₂)
  rw [mem_range_iff_of_ne hk hk'] at hw₁ hw₂
  have hw₁' : w₁ ≠ 0 := fun nh => by
    simp [nh] at hw₁
    rcases (show k ≤ -2 ∨ k ≥ 1 by omega) with hk | hk
    · nlinarith [show k ≤ (-2 : ℝ) from mod_cast hk, pi_pos]
    · nlinarith [show k ≥ (1 : ℝ) from mod_cast hk, pi_pos]
  have hw₂' : w₂ ≠ 0 := fun nh => by simp_all
  have hw₁w₂ : w₁.arg + w₁.im = w₂.arg + w₂.im :=
    arg_add_im_eq_of_mul_exp_eq_mem hw₁' hw₂' h hw₁ hw₂
  by_cases h_eq : w₁.arg + w₁.im = (2 * k + 1) * π
  · clear hw₁ hw₂
    have hz : w₁ * cexp w₁ ∈ Iio 0 ×ℂ {0} := by
      have : (w₁ * cexp w₁).arg = π := by
        rw [mul_exp_eq_of_arg_add_im_eq hw₁' h_eq, arg_neg_ofReal_of_pos <| Real.exp_pos _]
      rwa [arg_eq_pi_iff] at this
    obtain ⟨w, -, hw⟩ := existsUnique_eq_mul_exp_eq hk hk' (z := w₁ * cexp w₁) hz
    have Hw₁ := hw w₁ ⟨h_eq, rfl⟩
    have Hw₂ := hw w₂ ⟨hw₁w₂ ▸ h_eq, h.symm⟩
    exact Hw₂ ▸ Hw₁
  · have hz : w₁ * cexp w₁ ∈ Complex.slitPlane := by
      refine mem_slitPlane_iff_arg.mpr ⟨?_, by simp [hw₁']⟩
      grind [arg_mul_exp_eq_of_mem hw₁' hw₁]
    obtain ⟨w, -, hw⟩ := existsUnique_mem_Ioo_mul_exp_eq k (z := w₁ * cexp w₁) hz
    have Hw₁ := hw w₁ ⟨⟨hw₁.left, lt_of_le_of_ne hw₁.right h_eq⟩, rfl⟩
    have Hw₂ := hw w₂ ⟨⟨hw₂.left, lt_of_le_of_ne hw₂.right (hw₁w₂ ▸ h_eq)⟩, h.symm⟩
    exact Hw₂ ▸ Hw₁

theorem LambertW.injOn_mul_exp_range :
    InjOn (fun w => w * cexp w) (range k) := by
  rcases (show k = 0 ∨ k = -1 ∨ (k ≠ 0 ∧ k ≠ -1) by tauto) with rfl | rfl | ⟨hk, hk'⟩
  · exact injOn_mul_exp_range_zero
  · exact injOn_mul_exp_range_neg_one
  · exact injOn_mul_exp_range_of_ne hk hk'

theorem LambertW.surjOn_mul_exp_range :
    SurjOn (fun w => w * cexp w) (range k) (domain k) := by
  simpa only [← image_mul_exp_range] using surjOn_image _ _

theorem LambertW.bijOn_mul_exp_range_domain :
    BijOn (fun w => w * cexp w) (range k) (domain k) :=
  ⟨mapsTo_mul_exp_range, injOn_mul_exp_range, surjOn_mul_exp_range⟩

theorem LambertW.iUnion_range : ⋃ k, range k = univ := by
  refine eq_univ_iff_forall.mpr fun w => mem_iUnion.mpr ?_
  by_cases hw : w ∈ Iic (-1) ×ℂ {0}
  · use -1, Or.inr hw
  · obtain ⟨k, hk, -⟩ : ∃! k : ℤ, w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) :=
      Real.existsUnique_mem_Ioc (w.arg + w.im)
    use k
    rwa [mem_range_iff_of_notMem hw]

theorem LambertW.neg_one_notMem_range_of_ne (hk : k ≠ 0) (hk' : k ≠ -1) : -1 ∉ range k := by
  rw [mem_range_iff_of_ne hk hk']
  simp [field, pi_pos]
  norm_cast
  omega

theorem LambertW.eq_of_mem_range_of_mem_range {i j : ℤ} (hi : w ∈ range i) (hj : w ∈ range j)
    (hw : w ≠ -1) : i = j := by
  by_cases hw' : w ∈ Iic (-1) ×ℂ {0}
  · have hre : w.re ≠ -1 := fun hre => hw (Complex.ext hre (by simpa using hw'.right))
    grind [mem_range_iff_of_mem hw']
  · obtain ⟨k, -, hk⟩ := Real.existsUnique_mem_Ioc (w.arg + w.im)
    grind [mem_range_iff_of_notMem hw' |>.mp hi, mem_range_iff_of_notMem hw' |>.mp hj]

theorem LambertW.existsUnique_mem_range_of_ne_neg_one (hw : w ≠ -1) :
    ∃! k : ℤ, w ∈ range k := by
  obtain ⟨k, hk⟩ := mem_iUnion.mp <| eq_univ_iff_forall.mp iUnion_range w
  exact ⟨k, hk, fun k' hk' => eq_of_mem_range_of_mem_range hk' hk hw⟩

--  TODO
-- theorem LambertW.openRange_subset_range : openRange k ⊆ range k := by
--   grind [belowBondary_of_strictBelowBondary, openRange, range]

-- theorem LambertW.slitPlane_subset_domain : slitPlane k ⊆ domain k := by
--   unfold slitPlane domain
--   split_ifs with hk <;> simp [branchCut, hk, mem_reProdIm]

-- theorem LambertW.interior_range : interior (range k) = openRange k := by
--   sorry

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

theorem lambertW_mem_range_of_mem_domain
    (hz : z ∈ domain k) : W_ k z ∈ range k := by
  refine Function.invFunOn_mem ?_
  rwa [← mem_image, bijOn_mul_exp_range_domain.image_eq]

theorem lambertW_mul_exp_of_mem_range (hw : w ∈ range k) : W_ k (w * exp w) = w :=
  LambertW.bijOn_mul_exp_range_domain.invOn_invFunOn.left hw

theorem lambertW_mul_exp_lambertW_of_mem_domain (hz : z ∈ domain k) :
    W_ k z * cexp (W_ k z) = z := by
  apply Function.invFunOn_eq (f := fun w => w * exp w)
  rwa [← mem_image, bijOn_mul_exp_range_domain.image_eq]

@[simp]
theorem lambertW_zero_mul_exp_lambertW_zero : W₀ z * cexp (W₀ z) = z :=
  lambertW_mul_exp_lambertW_of_mem_domain trivial

theorem exists_eq_lambertW_of_eq_mul_exp (hw : z = w * cexp w) :
    ∃ k : ℤ, w = W_ k z ∧ z ∈ domain k := by
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := eq_univ_iff_forall.mp iUnion_range w
  refine ⟨k, hw ▸ lambertW_mul_exp_of_mem_range hk |>.symm, ?_⟩
  by_cases hz : z = 0
  · rw [hz] at hw ⊢
    simp at hw
    simp [hw, zero_mem_range_iff] at hk
    simp [hk]
  by_cases hk : k = 0
  · simp [hk]
  · simpa [domain_of_ne_zero hk]

theorem eq_mul_exp_iff_exists_eq_lambertW :
    z = w * cexp w ↔ ∃ k : ℤ, w = W_ k z ∧ z ∈ domain k := by
  refine ⟨exists_eq_lambertW_of_eq_mul_exp, fun ⟨k, hk, hz⟩ => ?_⟩
  rw [hk, lambertW_mul_exp_lambertW_of_mem_domain hz]

theorem existsUnique_eq_lambertW_of_ne_neg_one
    (hw : z = w * cexp w) (hw' : w ≠ -1) : ∃! k : ℤ, w = W_ k z ∧ z ∈ domain k := by
  obtain ⟨k, hk, Hk⟩ := existsUnique_mem_range_of_ne_neg_one hw'
  refine ⟨k, ⟨hw ▸ lambertW_mul_exp_of_mem_range hk |>.symm, ?_⟩,
    fun k' hk' => Hk k' <| hk'.1 ▸ lambertW_mem_range_of_mem_domain hk'.2⟩
  by_cases hk₀ : k = 0
  · simp [hk₀]
  · apply mem_domain_of_ne_zero fun hz => ne_zero_of_mem_range hk₀ hk ?_
    simp_all

section TODO
-- /-- **TODO** doc -/
-- theorem conj_lambertW_eq_lambertW_neg_conj (hz : z ∈ LambertW.slitPlane k) :
--     conj (W_ k z) = W_ (-k) (conj z) := by
--   sorry

-- theorem LambertW.isOpen_domain : IsOpen (domain k) := by
--   change (if _ then _ else _ : Set ℂ) ∈ {y | IsOpen y}
--   simp [ite_mem]

-- theorem LambertW.isClosed_branchCut : IsClosed (branchCut k) :=
--   isClosed_Iic.reProdIm isClosed_singleton

-- theorem LambertW.isOpen_slitPlane : IsOpen (slitPlane k) :=
--   isClosed_branchCut.isOpen_compl

-- private theorem LambertW.isOpen_openRange_zero : IsOpen (openRange 0) := by
--   suffices openRange 0 =
--       Complex.slitPlane ∩ (fun w => w.arg + w.im) ⁻¹' Ioo (-π) π ∪ Metric.ball 0 1 by
--     simpa only [this] using
--       continuousOn_arg_add_im.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo |>.union
--         Metric.isOpen_ball
--   rw [openRange_zero]
--   ext w
--   constructor
--   · rintro (hidx | ⟨hre, him⟩)
--     · by_cases hs : w ∈ Complex.slitPlane
--       · exact Or.inl ⟨hs, hidx⟩
--       rw [Complex.mem_slitPlane_iff, not_or, not_not, not_lt] at hs
--       obtain ⟨hre, him⟩ := hs
--       rcases lt_or_eq_of_le hre with hre | hre
--       · exact False.elim <| lt_irrefl π <|
--           arg_add_im_eq_pi_of_arg_eq_pi (arg_eq_pi_iff.mpr ⟨hre, him⟩) ▸ hidx.right
--       · exact Or.inr <| (Complex.ext (w := 0) hre him) ▸ Metric.mem_ball_self zero_lt_one
--     · rw [mem_preimage, mem_singleton_iff] at him
--       refine Or.inr <| mem_ball_zero_iff.mpr ?_
--       rw [Complex.ext (z := w) (w := w.re) rfl him, norm_real, norm_eq_abs, abs_of_neg hre.right]
--       linarith [hre.left]
--   rintro (⟨-, hidx⟩ | hb)
--   · exact Or.inl hidx
--   rw [mem_ball_zero_iff] at hb
--   by_cases harg : w.arg = π
--   · obtain ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp harg
--     refine Or.inr ⟨⟨?_, hre⟩, him⟩
--     rw [Complex.ext (z := w) (w := w.re) rfl him, norm_real, norm_eq_abs, abs_of_neg hre] at hb
--     linarith
--   left
--   replace harg : w.arg ∈ Ioo (-π) π := ⟨neg_pi_lt_arg w, lt_of_le_of_ne (arg_le_pi w) harg⟩
--   rw [mem_ofPred, ← norm_mul_sin_arg]
--   generalize w.arg = x at *
--   rw [show x + ‖w‖ * x.sin = (1 - ‖w‖) * x + ‖w‖ * (x + x.sin) by ring]
--   exact (convex_Ioo (-π) π) harg (add_sin_mem_Ioo_of_mem_Ioo harg)
--     (sub_nonneg_of_le hb.le) (norm_nonneg w) (sub_add_cancel 1 ‖w‖)

-- private theorem LambertW.isOpen_openRange_of_ne (hk : k ≠ 0) : IsOpen (openRange k) := by
--   suffices openRange k = Complex.slitPlane ∩
--       (fun w => w.arg + w.im) ⁻¹' Ioo ((2 * k - 1) * π) ((2 * k + 1) * π) by
--     simpa only [this] using
--       continuousOn_arg_add_im.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo
--   rw [openRange_of_ne_zero hk]
--   ext w
--   refine ⟨fun hw => ⟨Classical.byContradiction fun nh => ?_, hw⟩, And.right⟩
--   rw [mem_slitPlane_iff_arg, not_and_or, not_not, not_not] at nh
--   rw [mem_ofPred] at hw
--   rcases nh with nh | nh
--   · rw [arg_eq_pi_iff.mp nh |>.right, add_zero] at hw
--     simp [nh, field, sub_lt_iff_lt_add, one_add_one_eq_two] at hw
--     norm_cast at hw
--     omega
--   · simp [nh, field, pi_pos, mul_neg_iff, pi_pos.not_gt] at hw
--     norm_cast at hw
--     omega

-- theorem LambertW.isOpen_openRange : IsOpen (openRange k) :=
--   em (k = 0) |>.elim (fun hk => hk ▸ isOpen_openRange_zero) isOpen_openRange_of_ne

-- theorem _root_.continuousAt_clambertW {z : ℂ} (h : z ∈ LambertW.slitPlane k) :
--     ContinuousAt (W_ k) z := by
--   sorry

-- theorem _root_.Filter.Tendsto.clambertW {l : Filter α} {f : α → ℂ} {x : ℂ} (h : Tendsto f l (𝓝 x))
--     (hx : x ∈ LambertW.slitPlane k) : Tendsto (fun t => W_ k (f t)) l (𝓝 <| W_ k x) :=
--   (continuousAt_clambertW hx).tendsto.comp h

-- variable [TopologicalSpace α]

-- nonrec theorem _root_.ContinuousAt.clambertW {f : α → ℂ} {x : α} (h₁ : ContinuousAt f x)
--     (h₂ : f x ∈ LambertW.slitPlane k) : ContinuousAt (fun t => W_ k (f t)) x :=
--   h₁.clambertW h₂

-- nonrec theorem _root_.ContinuousWithinAt.clambertW {f : α → ℂ} {s : Set α} {x : α}
--     (h₁ : ContinuousWithinAt f s x) (h₂ : f x ∈ LambertW.slitPlane k) :
--     ContinuousWithinAt (fun t => W_ k (f t)) s x :=
--   h₁.clambertW h₂

-- nonrec theorem _root_.ContinuousOn.clambertW {f : α → ℂ} {s : Set α} (h₁ : ContinuousOn f s)
--     (h₂ : ∀ x ∈ s, f x ∈ LambertW.slitPlane k) : ContinuousOn (fun t => W_ k (f t)) s :=
--   fun x hx => (h₁ x hx).clambertW (h₂ x hx)

-- nonrec theorem _root_.Continuous.clambertW {f : α → ℂ} (h₁ : Continuous f)
--     (h₂ : ∀ x, f x ∈ LambertW.slitPlane k) : Continuous fun t => W_ k (f t) :=
--   continuous_iff_continuousAt.mpr fun x => h₁.continuousAt.clambertW (h₂ x)

-- /-- TODO doc -/
-- def mulExpOpenPartialHomeomorph : OpenPartialHomeomorph ℂ ℂ where
--   toFun := fun w => w * cexp w
--   invFun := lambertW k
--   source := LambertW.openRange k
--   target := LambertW.slitPlane k
--   map_source' := by
--     sorry
--   map_target' z h := by
--     sorry
--   left_inv' _x hx := apply_mul_exp_of_mem_range <| openRange_subset_range hx
--   right_inv' _x hx := apply_mul_exp_apply_of_mem_domain <| slitPlane_subset_domain hx
--   open_source := isOpen_openRange
--   open_target := LambertW.isOpen_slitPlane
--   continuousOn_toFun := by fun_prop
--   continuousOn_invFun := continuousOn_id.clambertW fun _ => id
end TODO

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

theorem invOn_lambertWZero_mul_exp :
    InvOn W₀ (fun x => x * rexp x) (Ici (-1)) (Ici (-(rexp 1)⁻¹)) := by
  sorry

theorem invOn_mul_exp_lambertWZero :
    InvOn (fun x => x * rexp x) W₀ (Ici (-(rexp 1)⁻¹)) (Ici (-1)) := by
  sorry

theorem invOn_lambertWNegOne_mul_exp :
    InvOn W₋₁ (fun x => x * rexp x) (Iic (-1)) (Ico (-(rexp 1)⁻¹) 0) := by
  sorry

theorem invOn_mul_exp_lambertWNegOne :
    InvOn (fun x => x * rexp x) W₋₁ (Ico (-(rexp 1)⁻¹) 0) (Iic (-1)) := by
  sorry

theorem bijOn_lambertWZero : BijOn W₀ (Ici (-(rexp 1)⁻¹)) (Ici (-1)) := by
  sorry

theorem bijOn_lambertWNegOne : BijOn W₋₁ (Ico (-(rexp 1)⁻¹) 0) (Iic (-1)) := by
  sorry

theorem lambertWZero_mul_exp_of_le (hx : -1 ≤ x) : W₀ (x * rexp x) = x := by
  sorry

theorem lambertWZero_mul_exp_lambertWZero_of_le (hx : -(rexp 1)⁻¹ ≤ x) :
    W₀ x * rexp (W₀ x) = x := by
  sorry

theorem lambertWNegOne_mul_exp_of_le (hx : x ≤ -1) : W₋₁ (x * rexp x) = x := by
  sorry

theorem lambertWNegOne_mul_exp_lambertWNegOne_of_le (hx : x ∈ Ico (-(rexp 1)⁻¹) 0) :
    W₋₁ x * rexp (W₋₁ x) = x := by
  sorry

theorem strictMonoOn_lambertWZero : StrictMonoOn W₀ (Ici (-(rexp 1)⁻¹)) := by
  sorry

theorem strictAntiOn_lambetWNegOne : StrictAntiOn W₋₁ (Ico (-(rexp 1)⁻¹) 0) := by
  sorry

@[simp]
theorem lambertWZero_zero : W₀ 0 = 0 := by
  nth_rw 1 [show 0 = 0 * rexp 0 from zero_mul _ |>.symm, lambertWZero_mul_exp_of_le]
  norm_num

theorem lambertWZero_pos_of_pos (hx : 0 < x) : 0 < W₀ x := by
  have : -(rexp 1)⁻¹ ≤ 0 := by simpa using exp_nonneg 1
  exact lambertWZero_zero ▸ strictMonoOn_lambertWZero this (this.trans hx.le) hx

theorem lambertWZero_nonneg_of_nonneg (hx : 0 ≤ x) : 0 ≤ W₀ x := by
  have : -(rexp 1)⁻¹ ≤ 0 := by simpa using exp_nonneg 1
  exact lambertWZero_zero ▸ strictMonoOn_lambertWZero.monotoneOn this (this.trans hx) hx

theorem lambertWZero_neg_of_lt (hx : x < -(rexp 1)⁻¹) : W₀ x < 0 := by
  sorry

theorem lambertWZero_neg_of_neg (hx : x < 0) : W₀ x < 0 := by
  rcases lt_or_ge x (-(rexp 1)⁻¹) with hx' | hx'
  · exact lambertWZero_neg_of_lt hx'
  · exact lambertWZero_zero ▸ strictMonoOn_lambertWZero hx' (hx'.trans hx.le) hx

theorem lambertWZero_nonpos_of_nonpos (hx : x ≤ 0) : W₀ x ≤ 0 := by
  rcases lt_or_ge x (-(rexp 1)⁻¹) with hx' | hx'
  · exact lambertWZero_neg_of_lt hx' |>.le
  · exact lambertWZero_zero ▸ strictMonoOn_lambertWZero.monotoneOn hx' (hx'.trans hx) hx

theorem lambertWZero_ne_zero_of_ne_zero (hx : x ≠ 0) : W₀ x ≠ 0 := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · exact lambertWZero_neg_of_neg hx |>.ne
  · exact lambertWZero_pos_of_pos hx |>.ne'

theorem lambertWNegOne_neg_of_ne_zero (hx : x ≠ 0) : W₋₁ x < 0 := by
  sorry

open Qq Mathlib.Meta.Positivity in
/-- TODO doc -/
@[positivity Real.lambertWZero _]
meta def _root_.Mathlib.Meta.Positivity.evalLambertWZero :
    PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(W₀ $a) =>
    assertInstancesCommute
    match ← core zα pα a with
    | .positive pa => pure <| .positive q(lambertWZero_pos_of_pos $pa)
    | .nonnegative pa => pure <| .nonnegative q(lambertWZero_nonneg_of_nonneg $pa)
    | .nonzero pa => pure <| .nonzero q(lambertWZero_ne_zero_of_ne_zero $pa)
    | _ => pure .none
  | _, _, _ => throwError "not Real.lambertWZero"

theorem zero_lt_omegaConstant : 0 < Ω := by
  positivity

theorem omegaConstant_lt_one : Ω < 1 := by
  sorry

--  TODO
-- theorem lambertWZero_add_lambertWZero_of_pos (hx : 0 < x) (hy : 0 < y) :
--     W₀ x + W₀ y = W₀ (x * y / W₀ x + x * y / W₀ y) := by
--   sorry

end Real

#lint
