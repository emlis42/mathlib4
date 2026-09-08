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

private theorem exists_add_log_eq (x : ℝ) : ∃ t > 0, t + log t = x :=
  continuousOn_id.add continuousOn_log |>.mono (by simp) |>.surjOn_of_tendsto
    nonempty_Ioi (tendsto_comp_coe_Ioi_atBot (Order.IsPredPrelimit.of_dense 0) |>.mpr <|
      tendsto_id.mono_left nhdsWithin_le_nhds |>.add_atBot tendsto_log_nhdsGT_zero)
        (tendsto_comp_val_Ioi_atTop.mpr <| tendsto_id.atTop_add_atTop tendsto_log_atTop) trivial

private theorem eq_of_log_add_self_eq {t₁ t₂ : ℝ} (h₁ : 0 < t₁) (h₂ : 0 < t₂)
    (h : Real.log t₁ + t₁ = Real.log t₂ + t₂) : t₁ = t₂ :=
  (strictMonoOn_log.add strictMonoOn_id).injOn h₁ h₂ h

end Real

namespace Complex

open Real Set

open scoped ComplexConjugate

variable {x y w z : ℂ} {i : ℤ}

theorem im_pos_of_arg (h : x.arg ∈ Ioo 0 π) : 0 < x.im := by
  rw [← norm_mul_sin_arg]
  apply mul_pos (norm_pos_iff.mpr fun nh => ?_) <| sin_pos_of_mem_Ioo h
  simp [nh] at h

theorem arg_neg_ofReal_of_pos {x : ℝ} (hx : 0 < x) : (-x : ℂ).arg = π := by
  rw [← ofReal_neg, arg_ofReal_of_neg <| neg_neg_iff_pos.mpr hx]

theorem arg_neg_ofReal_of_nonpos {x : ℝ} (hx : x ≤ 0) : (-x : ℂ).arg = 0 := by
  rw [← ofReal_neg, arg_ofReal_of_nonneg <| Right.nonneg_neg_iff.mpr hx]

private theorem arg_add_im_eq_pi_of_arg_eq_pi (h : x.arg = π) : x.arg + x.im = π := by
  simpa [(arg_eq_pi_iff.1 h).2]

theorem arg_mul_eq_add_arg_sub_iff (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).arg = x.arg + y.arg - 2 * π ↔ π < x.arg + y.arg := by
  constructor
  · intro h
    have h' := neg_pi_lt_arg (x * y)
    rw [h] at h'
    linarith
  · intro h
    have hmem : x.arg + y.arg - 2 * π ∈ Set.Ioc (-π) π := by
      have hx' := arg_le_pi x
      have hy' := arg_le_pi y
      constructor <;> [linarith; linarith]
    have hcoe : ((x.arg + y.arg : ℝ) : Real.Angle) = ((x.arg + y.arg - 2 * π : ℝ) : Real.Angle) := by
      simp [Real.Angle.coe_sub, Real.Angle.coe_two_pi]
    rw [← arg_coe_angle_toReal_eq_arg, arg_mul_coe_angle hx hy, ← Real.Angle.coe_add, hcoe]
    exact Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.2 hmem

theorem arg_mul_eq_add_arg_add_iff (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).arg = x.arg + y.arg + 2 * π ↔ x.arg + y.arg ≤ - π:= by
  sorry

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

-- private theorem re_add_log_eq (x : ℂ) : (x + log x).re = Real.log ‖x‖ + ‖x‖ * Real.cos x.arg := by
--   simp [Complex.log_re, add_comm]

-- private theorem add_log_re (w : ℂ) : (w + log w).re = Real.log ‖w‖ + w.re := by
--   rw [Complex.add_re, Complex.log_re, add_comm]

-- private theorem re_add_log_le_neg_one {t : ℝ} (ht : 0 < t) : ((-t) + log (-t)).re ≤ -1 := by
--   simp [log_re, abs_of_pos ht]
--   linarith [log_le_sub_one_of_pos ht]

private theorem exp_add_log_of_ne_zero (hx : x ≠ 0) : cexp (x + x.log) = x * cexp x := by
  rw [exp_add, exp_log hx, mul_comm]

private theorem add_log_im : (x + x.log).im = x.arg + x.im := by
  simp [log, add_comm]

-- private theorem arg_neg_ofReal {x : ℝ} (hx : 0 < x) : (-x : ℂ).arg = π := by
--   simpa [arg_eq_pi_iff]

-- private theorem neg_add_log_neg {x : ℝ} (hx : 0 < x) :
--     (-x) + log (-x) = ⟨Real.log x - x, π⟩ := by
--   refine ext ?_ ?_
--   · simp [log_re, neg_add_eq_sub]
--   · rw [add_log_im, arg_neg_ofReal hx, neg_im, ofReal_im, neg_zero, add_zero]

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

private theorem exists_arg_mul_exp_eq (hx : x ≠ 0) :
    ∃ k : ℤ, (x * cexp x).arg = x.arg + x.im + k * (2 * π) := by
  obtain ⟨m, hm⟩ := exists_arg_mul_eq_add_arg hx (exp_ne_zero x)
  use m - toIocDiv two_pi_pos (-π) x.im
  grind [arg_exp, toIocMod]

private theorem exp_add_log (hw : w ≠ 0) : exp (w + log w) = w * exp w := by
  rw [add_comm, exp_add, exp_log hw]

private theorem mul_exp_eq_of_arg_add_im_eq (hx : x ≠ 0) (h : x.arg + x.im = (2 * i + 1) * π) :
    x * cexp x = -rexp (x + log x).re := by
  rw [← exp_add_log hx]
  apply Complex.ext
  · rw [exp_re, add_log_im, h, show (2 * i + 1) * π = i * (2 * π) + π by ring,
      Real.cos_int_mul_two_pi_add_pi i, neg_re, ofReal_re, mul_neg_one]
  · rw [exp_im, add_log_im, h, show (2 * i + 1) * π = ((2 * i + 1 : ℤ) : ℝ) * π by grind,
      Real.sin_int_mul_pi _, mul_zero, neg_im, ofReal_im, neg_zero]

end Complex

section Solve

open Real Complex ComplexConjugate Set Filter Topology

variable {ρ θ : ℝ}

namespace Real

def LambertW.solutionArgAux (θ : ℝ) : ℝ -> ℝ := fun ϕ =>
  (θ - ϕ) / sin ϕ

def LambertW.solutionNormAux (θ : ℝ) : ℝ -> ℝ := fun ϕ =>
  solutionArgAux θ ϕ * rexp (solutionArgAux θ ϕ * cos ϕ)

--  this needs annotations
private theorem LambertW.exists_mem_Ioo (hθ1 : θ ≠ π) (hθ2 : 0 < θ) (hρ : 0 < ρ) :
    ∃ ϕ ∈ Ioo 0 (θ ⊓ π),
      (θ - ϕ) / sin ϕ * rexp ((θ - ϕ) / sin ϕ * cos ϕ) = ρ := by
  set r : ℝ -> ℝ := fun ϕ => (θ - ϕ) / sin ϕ
  change ∃ ϕ ∈ Ioo 0 (θ ⊓ π), r ϕ * rexp (r ϕ * cos ϕ) = ρ
  have hrcont : ContinuousOn r (Ioo 0 (min θ π)) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun ϕ hϕ =>
      (sin_pos_of_pos_of_lt_pi hϕ.left <| hϕ.right.trans_le <| min_le_right θ π).ne'
  have hρcont : ContinuousOn (fun ϕ => r ϕ * rexp (r ϕ * cos ϕ)) (Ioo 0 (min θ π)) :=
    hrcont.mul <| hrcont.mul continuous_cos.continuousOn |>.rexp
  have hr₀ : Tendsto r (𝓝[>] 0) atTop := by
    have : Tendsto sin (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · simpa using (continuous_sin.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT pi_pos] with x hx using sin_pos_of_pos_of_lt_pi hx.1 hx.2
    replace this : Tendsto (fun x ↦ (θ - x) * (sin x)⁻¹) (𝓝[>] 0) atTop :=
      (continuous_const.sub continuous_id).tendsto 0 |>.mono_left nhdsWithin_le_nhds
        |>.pos_mul_atTop (sub_pos.mpr hθ2) <| tendsto_inv_nhdsGT_zero.comp this
    simpa [r, div_eq_mul_inv] using this
  refine isPreconnected_Ioo.intermediate_value_Ioi
    (le_principal_iff.mpr <| Ioo_mem_nhdsLT <| lt_min hθ2 pi_pos)
      (le_principal_iff.mpr <| Ioo_mem_nhdsGT <| lt_min hθ2 pi_pos)
        hρcont ?_ ?_ hρ
  · rcases lt_or_gt_of_ne hθ1 with hθ1 | hθ1
    · rw [min_eq_left hθ1.le]
      have : ContinuousAt r θ :=
        ContinuousAt.div (by fun_prop) (by fun_prop) <| sin_pos_of_pos_of_lt_pi hθ2 hθ1 |>.ne'
      replace this : ContinuousAt (fun ϕ => r ϕ * rexp (r ϕ * cos ϕ)) θ :=
        this.mul <| this.mul continuous_cos.continuousAt |>.rexp
      convert this.tendsto.mono_left nhdsWithin_le_nhds using 2
      simp [r]
    · rw [min_eq_right hθ1.le]
      apply squeeze_zero' (g := fun ϕ => r ϕ * rexp (-(r ϕ) / 2))
      · filter_upwards [Ioo_mem_nhdsLT pi_pos] with x hx using
          mul_nonneg (div_nonneg (by grind) (by grind [sin_pos_of_pos_of_lt_pi])) (exp_nonneg _)
      · filter_upwards [Ioo_mem_nhdsLT (a := π - π / 3) (by grind [pi_pos])] with x hx
        have hr : 0 ≤ r x := div_nonneg (by linarith [hx.2]) <| le_of_lt <|
          sin_pos_of_pos_of_lt_pi (by linarith [pi_pos, hx.1]) hx.2
        have hcos : cos x ≤ -(1 / 2) := by
          grw [cos_le_cos_of_nonneg_of_le_pi (by grind) hx.2.le hx.1.le,
            cos_pi_sub, cos_pi_div_three]
        exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith)) hr
      · apply Filter.Tendsto.comp (f := r) (g := fun r => r * rexp (-r / 2)) (y := atTop) ?_ ?_
        · convert (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 |>.comp <|
            tendsto_id.atTop_div_const zero_lt_two).const_mul 2 using 2
          · simp [field]
          · simp
        · have : Tendsto sin (𝓝[<] π) (𝓝[>] 0) := by
            apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
            · simpa using (continuous_sin.tendsto π).mono_left nhdsWithin_le_nhds
            · filter_upwards [Ioo_mem_nhdsLT pi_pos] with x hx using
                sin_pos_of_pos_of_lt_pi hx.1 hx.2
          replace this := ((continuous_const.sub continuous_id).tendsto π).mono_left
            nhdsWithin_le_nhds |>.pos_mul_atTop (sub_pos.mpr hθ1) <|
              tendsto_inv_nhdsGT_zero.comp this
          simpa [r, div_eq_mul_inv] using this
  · refine tendsto_atTop_mono' _ ?_ hr₀
    filter_upwards [Ioo_mem_nhdsGT (a := θ ⊓ (π / 2)) (by grind [pi_pos])] with ϕ hϕ
    nth_rw 1 [← mul_one (r ϕ)]
    have hrϕ : 0 ≤ r ϕ := div_nonneg (by grind) (by grind [sin_pos_of_pos_of_lt_pi])
    gcongr
    apply one_le_exp (mul_nonneg hrϕ ?_)
    grind [cos_pos_of_mem_Ioo]

end Real

namespace Complex

--  this needs annotations
private theorem LambertW.exists_eq_mul_exp_eq_of_pos (hθ1 : θ ≠ π) (hθ2 : 0 < θ) (hρ : 0 < ρ) :
    ∃ w : ℂ, w.arg + w.im = θ ∧ w * cexp w = ρ * cexp (θ * I) := by
  set r : ℝ -> ℝ := fun ϕ => (θ - ϕ) / Real.sin ϕ
  obtain ⟨ϕ, hϕ, hrρ⟩ := Real.LambertW.exists_mem_Ioo hθ1 hθ2 hρ
  change r ϕ * rexp (r ϕ * Real.cos ϕ) = ρ at hrρ
  have hsϕ : 0 < Real.sin ϕ :=
    Real.sin_pos_of_pos_of_lt_pi hϕ.left <| hϕ.right.trans_le <| min_le_right θ π
  have hr : 0 < r ϕ := by
    unfold r
    refine div_pos_iff_of_pos_left ?_ |>.mpr hsϕ
    simpa using hϕ.right.trans_le <| min_le_left θ π
  refine ⟨r ϕ * cexp (ϕ * I), ?_, ?_⟩
  · rw [exp_ofReal_mul_I, ofReal_cos, ofReal_sin, arg_mul_cos_add_sin_mul_I hr (by grind)]
    simp [sin_ofReal_re]
    grind
  · calc
      _ = ↑(r ϕ * rexp (r ϕ * Real.cos ϕ)) * cexp (↑(ϕ + r ϕ * Real.sin ϕ) * I) := by
        nth_rw 2 [exp_mul_I]
        rw [mul_add, exp_add, ofReal_add, add_mul, exp_add]
        simp
        ring_nf
      _ = ρ * cexp (θ * I) := by grind

private theorem LambertW.exists_eq_mul_exp_eq (hθ1 : θ ≠ π) (hθ2 : θ ≠ -π) (hρ : 0 < ρ) :
    ∃ w : ℂ, w.arg + w.im = θ ∧ w * cexp w = ρ * cexp (θ * I) := by
  rcases lt_trichotomy θ 0 with hθ' | rfl | hθ'
  · obtain ⟨w, hw1, hw2⟩ : ∃ w : ℂ, w.arg + w.im = -θ ∧ w * cexp w = ρ * cexp (↑(-θ) * I) :=
      exists_eq_mul_exp_eq_of_pos (θ := -θ) (by grind) (by linarith) hρ
    refine ⟨conj w, ?_, ?_⟩
    · simp [arg_conj, show w.arg ≠ π by grind [arg_eq_pi_iff], ← neg_add, hw1]
    · rw [exp_conj, ← map_mul, hw2, map_mul, conj_ofReal,
        ← exp_conj, map_mul, conj_I, conj_ofReal, ofReal_neg, neg_mul_neg]
  · rw [ofReal_zero, zero_mul, exp_zero, mul_one]
    obtain ⟨x, hx⟩ := exists_add_log_eq (Real.log ρ)
    refine ⟨x, ?_, ?_⟩
    · simp [arg_eq_zero_iff, hx.left.le]
    · apply Complex.ext
      · simp only [mul_re, ofReal_re, ofReal_im, exp_ofReal_im, mul_zero, sub_zero, exp_ofReal_re]
        rw [← Real.exp_log hρ, ← hx.right, Real.exp_add, Real.exp_log hx.left, mul_comm]
      · simp
  · exact exists_eq_mul_exp_eq_of_pos hθ1 hθ' hρ

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
  set θ := z.arg + k * (2 * π) with hθ
  set ρ := ‖z‖
  have hz' : z = ρ * cexp (θ * I) := by
    rw [← norm_mul_exp_arg_mul_I z, hθ, ofReal_add, add_mul,
      mul_comm 2, ofReal_mul, ofReal_mul, ofReal_intCast, ofReal_ofNat,
      mul_assoc, mul_comm _ 2, exp_periodic.int_mul k]
  have hθ' : z.arg ∈ Ioo (-π) π :=
    ⟨arg_mem_Ioc z |>.left, lt_of_le_of_ne (arg_mem_Ioc z |>.right) <| slitPlane_arg_ne_pi hz⟩
  have hθ1 : θ ≠ π := by
    rcases (show k ≤ 0 ∨ k ≥ 1 by omega) with hk | hk <;> [apply ne_of_lt; apply ne_of_gt]
      <;> grw [hθ, hk] <;> grind
  have hθ2 : θ ≠ -π := by
    rcases (show k ≤ -1 ∨ k ≥ 0 by omega) with hk | hk <;> [apply ne_of_lt; apply ne_of_gt]
      <;> grw [hθ, hk] <;> grind
  obtain ⟨w, hw, hwz⟩ := exists_eq_mul_exp_eq hθ1 hθ2 (norm_pos_iff.mpr <| slitPlane_ne_zero hz)
  exact ⟨w, by grind, by grind⟩

private theorem LambertW.existsUnique_mem_Ioo_mul_exp_eq (k : ℤ) (hz : z ∈ Complex.slitPlane) :
    ∃! w : ℂ, w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π) ∧ w * cexp w = z := by
  sorry
  -- obtain ⟨w, ⟨hwl, hwr⟩, hwz⟩ := exists_mem_Ioo_mul_exp_eq k hz
  -- use w, ⟨⟨hwl, hwr⟩, hwz⟩
  -- intro w' ⟨⟨hw'l, hw'r⟩, hw'z⟩
  -- have hz : z ≠ 0 := slitPlane_ne_zero hz
  -- have := add_log_eq_of_mul_exp_eq_of_lt (by grind) (by grind) (hwz ▸ hw'z)
  --   (by apply abs_sub_lt_iff.mpr ⟨?_, ?_⟩ <;> linarith)
  -- -- refine eq_of_add_log_eq_of_arg_add_im_pos (by grind) (by grind) ?_ this ?_

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
  rcases lt_trichotomy z.re (-(rexp 1)⁻¹) with hz'' | hz'' | hz''
  · replace hz'' : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, -, hw⟩ := existsUnique_eq_pi_mul_exp_eq hz''
    have Hw₁ := hw w₁ ⟨hw₁.left.left, hw₁', hz₁.symm⟩
    have Hw₂ := hw w₂ ⟨hw₂.left.left, hw₂', hz₂.symm⟩

    sorry
  · sorry
  · replace hz'' : z ∈ Ioo (-(rexp 1)⁻¹) 0 ×ℂ {0} := by
      simp [mem_reProdIm] at hz' ⊢
      tauto
    obtain ⟨w, -, hw⟩ := existsUnique_Ioo_exp_eq hz''
    have Hw₁ := hw w₁ ⟨hw₁.left.left, hw₁', hz₁.symm⟩
    have Hw₂ := hw w₂ ⟨hw₂.left.left, hw₂', hz₂.symm⟩

private theorem LambertW.injOn_mul_exp_range_neg_one :
    InjOn (fun w => w * cexp w) (range (-1)) := by
  sorry

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
      obtain ⟨k', hk'⟩ := exists_arg_mul_exp_eq hw₁'
      rw [hk']
      rcases (show k' ≤ -k ∨ k' ≥ -k + 1 by omega) with hk | hk
      · apply ne_of_lt
        grw [hk, Int.cast_neg]
        nlinarith [lt_of_le_of_ne hw₁.right h_eq]
      · apply ne_of_gt
        grw [hk, Int.cast_add, Int.cast_neg, Int.cast_one]
        nlinarith [hw₁.left, pi_pos]
    obtain ⟨w, -, hw⟩ := existsUnique_mem_Ioo_mul_exp_eq k (z := w₁ * cexp w₁) hz
    have Hw₁ := hw w₁ ⟨⟨hw₁.left, lt_of_le_of_ne hw₁.right h_eq⟩, rfl⟩
    have Hw₂ := hw w₂ ⟨⟨hw₂.left, lt_of_le_of_ne hw₂.right (hw₁w₂ ▸ h_eq)⟩, h.symm⟩
    exact Hw₂ ▸ Hw₁

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
    ∃! k : ℤ, w ∈ range k := by
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
    ∃ k : ℤ, w = W_ k z ∧ z ∈ domain k := by
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
    z = w * cexp w ↔ ∃ k : ℤ, w = W_ k z ∧ z ∈ domain k := by
  refine ⟨exists_eq_lambertW_of_eq_mul_exp, fun ⟨k, hk, hz⟩ => ?_⟩
  rw [hk, apply_mul_exp_apply_of_mem_domain hz]

theorem existsUnique_eq_lambertW_of_ne_neg_inv_exp_one
    (hz : z ≠ -(exp 1)⁻¹) (hw : z = w * cexp w) : ∃! k : ℤ, w = W_ k z ∧ z ∈ domain k := by
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
  nth_rw 1 [show 0 = 0 * rexp 0 from zero_mul _ |>.symm, lambertWZero_mul_exp_of_le]
  norm_num

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
