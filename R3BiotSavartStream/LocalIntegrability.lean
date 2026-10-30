/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman.

# Local integrability of the Biot–Savart integrand for continuous compactly supported fields
-/
import R3BiotSavartStream.Refutation

open MeasureTheory Filter Topology

namespace R3BiotSavart

open NavierStokes3D ArnoldGeometric FrohmanianTether

theorem norm_cross_le (a b : EuclideanSpace ℝ (Fin 3)) : ‖cross a b‖ ≤ ‖a‖ * ‖b‖ := by
  have hsq : ‖cross a b‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp [cross, cross_apply, Fin.sum_univ_three]
    nlinarith [sq_nonneg (a 0 * b 0 + a 1 * b 1 + a 2 * b 2)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hsq

theorem continuous_cross : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
    cross p.1 p.2) := by
  unfold cross
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun i => ?_
  have h : ∀ j : Fin 3, Continuous fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (WithLp.ofLp p.1) j := fun j => (PiLp.continuous_apply 2 _ j).comp continuous_fst
  have h' : ∀ j : Fin 3, Continuous fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (WithLp.ofLp p.2) j := fun j => (PiLp.continuous_apply 2 _ j).comp continuous_snd
  fin_cases i <;> simp [cross_apply] <;> fun_prop

theorem measurable_kernelProfile : Measurable kernelProfile := by
  unfold kernelProfile
  refine Measurable.ite (by simpa using measurableSet_singleton (0 : T3)) measurable_const ?_
  exact measurable_const.mul (continuous_norm.measurable.pow_const _)

/-- `z ↦ 1_{‖z‖<R} ‖z‖⁻²` is integrable on `ℝ³`. -/
theorem integrable_indicator_ball_rpow_neg_two (R : ℝ) :
    Integrable (Set.indicator (Metric.ball (0 : T3) R) (fun z : T3 => ‖z‖ ^ (-2 : ℝ)))
      MeasureTheory.volume := by
  have hfun : Set.indicator (Metric.ball (0 : T3) R) (fun z : T3 => ‖z‖ ^ (-2 : ℝ)) =
      fun z => (fun r : ℝ => if r < R then r ^ (-2 : ℝ) else 0) ‖z‖ := by
    funext z
    by_cases h : ‖z‖ < R
    · simp [Set.indicator_of_mem (mem_ball_zero_iff.mpr h), h]
    · simp [Set.indicator_of_notMem (fun hm => h (mem_ball_zero_iff.mp hm)), h]
  rw [hfun]
  refine (integrable_fun_norm_addHaar (μ := MeasureTheory.volume)
    (f := fun r : ℝ => if r < R then r ^ (-2 : ℝ) else 0)).mpr ?_
  have hdim : Module.finrank ℝ T3 = 3 := finrank_euclideanSpace_fin
  rw [hdim]
  have hIoo : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 R) :=
    integrableOn_const (by simp) (by simp)
  have h1 : IntegrableOn (fun y : ℝ => y ^ (3 - 1) • (if y < R then y ^ (-2 : ℝ) else 0))
      (Set.Ioo 0 R) := by
    refine hIoo.congr_fun (fun y hy => ?_) measurableSet_Ioo
    have hy0 : (0 : ℝ) < y := hy.1
    simp only [smul_eq_mul, if_pos hy.2]
    rw [show (3 - 1 : ℕ) = 2 from rfl, ← Real.rpow_natCast, ← Real.rpow_add hy0]
    norm_num
  refine h1.of_forall_diff_eq_zero measurableSet_Ioi (fun y hy => ?_)
  have hy0 : (0 : ℝ) < y := hy.1
  have hyR : ¬ y < R := fun h => hy.2 ⟨hy0, h⟩
  simp [hyR]

/-- **Local integrability.** For continuous compactly supported `f`, the Biot–Savart integrand
`y ↦ K(x,y) (f y × (x - y))` is Lebesgue integrable at every `x`. -/
theorem integrable_biotSavart_integrand {f : T3 → EuclideanSpace ℝ (Fin 3)}
    (hc : Continuous f) (hs : HasCompactSupport f) (x : T3) :
    Integrable (fun y => biotSavartKernel x y • cross (f y) (x - y)) NavierStokes3D.volume := by
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  obtain ⟨R0, hR0⟩ := hs.isCompact.isBounded.subset_closedBall 0
  set R := R0 + ‖x‖ + 1
  have hdom : Integrable (fun y : T3 => (M * (4 * Real.pi)⁻¹) *
      Set.indicator (Metric.ball (0 : T3) R) (fun z : T3 => ‖z‖ ^ (-2 : ℝ)) (x - y))
      MeasureTheory.volume :=
    ((integrable_indicator_ball_rpow_neg_two R).comp_sub_left x).const_mul _
  have hmeas : AEStronglyMeasurable (fun y => biotSavartKernel x y • cross (f y) (x - y))
      MeasureTheory.volume := by
    simp_rw [biotSavartKernel_eq_profile]
    refine (Measurable.smul (measurable_kernelProfile.comp (measurable_const.sub measurable_id))
      ?_).aestronglyMeasurable
    exact (continuous_cross.comp (hc.prodMk (continuous_const.sub continuous_id))).measurable
  refine hdom.mono' hmeas (Eventually.of_forall fun y => ?_)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
  have hRHS : 0 ≤ (M * (4 * Real.pi)⁻¹) *
      Set.indicator (Metric.ball (0 : T3) R) (fun z : T3 => ‖z‖ ^ (-2 : ℝ)) (x - y) := by
    refine mul_nonneg (by positivity) (Set.indicator_nonneg (fun z _ => by positivity) _)
  by_cases hfy : f y = 0
  · simpa [hfy, cross] using hRHS
  by_cases hxy : x = y
  · subst hxy
    have : cross (f x) (x - x) = 0 := by ext i; fin_cases i <;> simp [cross, cross_apply]
    have hk : biotSavartKernel x x = 0 := by simp [biotSavartKernel]
    rw [hk, zero_smul, norm_zero]; exact hRHS
  have hy : y ∈ tsupport f := subset_tsupport _ hfy
  have hyb := hR0 hy
  rw [Metric.mem_closedBall, dist_zero_right] at hyb
  have hball : x - y ∈ Metric.ball (0 : T3) R := by
    rw [mem_ball_zero_iff]
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ < R := by simp only [R]; linarith
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [Set.indicator_of_mem hball, biotSavartKernel_of_ne' hxy, norm_smul,
    Real.norm_of_nonneg (by positivity)]
  calc (4 * Real.pi)⁻¹ * ‖x - y‖ ^ (-(3 : ℝ)) * ‖cross (f y) (x - y)‖
      ≤ (4 * Real.pi)⁻¹ * ‖x - y‖ ^ (-(3 : ℝ)) * (M * ‖x - y‖) := by
        refine mul_le_mul_of_nonneg_left ((norm_cross_le _ _).trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)
    _ = M * (4 * Real.pi)⁻¹ * ‖x - y‖ ^ (-2 : ℝ) := by
        rw [show (-2 : ℝ) = -(3 : ℝ) + 1 by norm_num, Real.rpow_add hpos, Real.rpow_one]
        ring

end R3BiotSavart
