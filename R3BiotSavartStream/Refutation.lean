/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman.
-/
import R3BiotSavartStream.Ported

open MeasureTheory Filter Topology

namespace R3BiotSavart

open NavierStokes3D ArnoldGeometric FrohmanianTether

/-- `z ↦ ‖z‖⁻²` is not integrable on `ℝ³` (it decays too slowly at infinity). -/
theorem not_integrable_norm_rpow_neg_two :
    ¬ Integrable (fun z : T3 => ‖z‖ ^ (-2 : ℝ)) MeasureTheory.volume := by
  intro h
  have h' := (integrable_fun_norm_addHaar (E := T3) MeasureTheory.volume
    (f := fun r : ℝ => r ^ (-2 : ℝ))).mp h
  have hdim : Module.finrank ℝ T3 = 3 := finrank_euclideanSpace_fin
  rw [hdim] at h'
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioi 0) := by
    refine h'.congr_fun (fun r hr => ?_) measurableSet_Ioi
    have hr : (0 : ℝ) < r := hr
    simp only [smul_eq_mul]
    rw [show (3 - 1 : ℕ) = 2 from rfl, ← Real.rpow_natCast, ← Real.rpow_add hr]
    norm_num
  rw [integrableOn_const_iff] at hone
  simp at hone

/-- Translation form of the kernel. -/
noncomputable def kernelProfile (z : T3) : ℝ :=
  if z = 0 then 0 else (4 * Real.pi)⁻¹ * ‖z‖ ^ (-(3 : ℝ))

theorem biotSavartKernel_eq_profile (x y : T3) :
    biotSavartKernel x y = kernelProfile (x - y) := by
  unfold biotSavartKernel kernelProfile
  by_cases h : x = y
  · simp [h]
  · simp [h, sub_eq_zero]

theorem biotSavartKernel_of_ne' {x y : T3} (h : x ≠ y) :
    biotSavartKernel x y = (4 * Real.pi)⁻¹ * ‖x - y‖ ^ (-(3 : ℝ)) := by
  simp [biotSavartKernel, h]

theorem cross_add_smul (a b v : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    cross (a + t • b) v = cross a v + t • cross b v := by
  unfold cross
  simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]

theorem norm_sq_cross_single (i : Fin 3) (z : EuclideanSpace ℝ (Fin 3)) :
    ‖cross (EuclideanSpace.single i 1) z‖ ^ 2 = ‖z‖ ^ 2 - z i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  fin_cases i <;>
    simp [cross, cross_apply, Fin.sum_univ_three] <;> ring

theorem norm_le_sum_norm_cross (z : EuclideanSpace ℝ (Fin 3)) :
    ‖z‖ ≤ ∑ i : Fin 3, ‖cross (EuclideanSpace.single i 1) z‖ := by
  have h0 := norm_sq_cross_single 0 z
  have h1 := norm_sq_cross_single 1 z
  have h2 := norm_sq_cross_single 2 z
  have hz : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_three]
  rw [Fin.sum_univ_three]
  set a := ‖cross (EuclideanSpace.single (0 : Fin 3) 1) z‖
  set b := ‖cross (EuclideanSpace.single (1 : Fin 3) 1) z‖
  set c := ‖cross (EuclideanSpace.single (2 : Fin 3) 1) z‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have hsq : ‖z‖ ^ 2 ≤ (a + b + c) ^ 2 := by
    nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 2), mul_nonneg ha hb,
      mul_nonneg hb hc, mul_nonneg ha hc]
  exact (pow_le_pow_iff_left₀ (norm_nonneg z) (by positivity) (by norm_num)).mp hsq

/-- Some constant direction `c` has a non-integrable Biot–Savart integrand at every point. -/
theorem exists_const_not_integrable :
    ∃ c : EuclideanSpace ℝ (Fin 3), ∀ x : T3,
      ¬ Integrable (fun y => biotSavartKernel x y • cross c (x - y)) NavierStokes3D.volume := by
  by_contra hcon
  push Not at hcon
  have hz : ∀ i : Fin 3, Integrable
      (fun z : T3 => kernelProfile z • cross (EuclideanSpace.single i 1) z)
      MeasureTheory.volume := by
    intro i
    obtain ⟨x, hx⟩ := hcon (EuclideanSpace.single i 1)
    have := (show Integrable _ MeasureTheory.volume from hx).comp_sub_left x
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp [biotSavartKernel_eq_profile]
  have hsum : Integrable (fun z : T3 => ∑ i : Fin 3,
      ‖kernelProfile z • cross (EuclideanSpace.single i 1) z‖) MeasureTheory.volume :=
    integrable_finset_sum _ (fun i _ => (hz i).norm)
  apply not_integrable_norm_rpow_neg_two
  have hdom : Integrable (fun z : T3 => (4 * Real.pi) * ∑ i : Fin 3,
      ‖kernelProfile z • cross (EuclideanSpace.single i 1) z‖) MeasureTheory.volume :=
    hsum.const_mul _
  refine hdom.mono' ((continuous_norm.measurable.pow_const _).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
  by_cases h0 : z = 0
  · subst h0
    rw [norm_zero, Real.zero_rpow (by norm_num), norm_zero]
    positivity
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr h0
  have hK : kernelProfile z = (4 * Real.pi)⁻¹ * ‖z‖ ^ (-(3 : ℝ)) := by
    simp [kernelProfile, h0]
  have hKnn : 0 ≤ kernelProfile z := by rw [hK]; positivity
  simp_rw [norm_smul, Real.norm_of_nonneg hKnn, ← Finset.mul_sum, Real.norm_of_nonneg
    (Real.rpow_nonneg (norm_nonneg z) _)]
  rw [hK]
  have hpi : (4 * Real.pi) * ((4 * Real.pi)⁻¹ * ‖z‖ ^ (-(3 : ℝ))) = ‖z‖ ^ (-(3 : ℝ)) := by
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  rw [← mul_assoc, hpi]
  have hle := norm_le_sum_norm_cross z
  calc ‖z‖ ^ (-2 : ℝ) = ‖z‖ ^ (-(3 : ℝ)) * ‖z‖ := by
        rw [show (-2 : ℝ) = -(3 : ℝ) + 1 by norm_num, Real.rpow_add hzpos, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (by positivity)

theorem orbit_zero_smul (ω : CoadjointOrbit) (c : EuclideanSpace ℝ (Fin 3)) (p) :
    (⟨fun x => ω.val x + (0 : ℝ) • c, p⟩ : CoadjointOrbit) = ω := by
  cases ω; simp

/-- **Refutation.** On `ℝ³`, if `ω` is differentiable, its Biot–Savart integral converges at every
point, and its kinetic energy is nonzero, then the kinetic energy has *no* Gâteaux representative
in the sense of `IsGateauxRepresentative`: that definition tests against every differentiable
divergence-free direction, including constant fields, whose Biot–Savart integral diverges. -/
theorem not_isGateauxRepresentative_kineticEnergy (ω : CoadjointOrbit)
    (hω : ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (hloc : ∀ x, Integrable (fun y => biotSavartKernel x y • cross (ω.val y) (x - y))
      NavierStokes3D.volume)
    (hH : KineticEnergyHamiltonian ω ≠ 0) (δ : T3 → EuclideanSpace ℝ (Fin 3)) :
    ¬ IsGateauxRepresentative KineticEnergyHamiltonian ω δ := by
  intro hrep
  obtain ⟨c, hc⟩ := exists_const_not_integrable
  let ε : CoadjointOrbit := ⟨fun _ => c, div_const c⟩
  have hε : ∀ i x, DifferentiableAt ℝ (fun y => ε.val y i) x := fun i _ => differentiableAt_const (c i)
  have h := hrep ε hω hε
  set f := fun t : ℝ => KineticEnergyHamiltonian ⟨fun x => ω.val x + t • ε.val x,
        fun x => orbit_add_smul_div_free ω ε t hω hε x⟩ with hf
  have hzero : ∀ t : ℝ, t ≠ 0 → f t = 0 := by
    intro t ht
    have hBS : BiotSavart (fun x => ω.val x + t • ε.val x) = 0 := by
      funext x
      refine integral_undef (fun hint => hc x ?_)
      have hdiff := MeasureTheory.Integrable.smul t⁻¹ (MeasureTheory.Integrable.sub hint (hloc x))
      refine hdiff.congr (Eventually.of_forall fun y => ?_)
      simp only [Pi.smul_apply, Pi.sub_apply, ε]
      rw [cross_add_smul, smul_add, smul_comm, add_sub_cancel_left, smul_smul,
        inv_mul_cancel₀ ht, one_smul]
    simp only [hf, KineticEnergyHamiltonian, hBS]
    simp
  have hcont := h.continuousAt
  have h1 : Tendsto f (𝓝[≠] 0) (𝓝 (f 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[≠] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hzero t ht).symm)
  have h0 : f 0 = 0 := tendsto_nhds_unique h1 h2
  apply hH
  rw [← h0, hf]
  simp only
  rw [orbit_zero_smul]

/-- **Refutation of `RegularStreamRepresentative`** under the same hypotheses. -/
theorem not_regularStreamRepresentative (ω : CoadjointOrbit)
    (hω : ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (hloc : ∀ x, Integrable (fun y => biotSavartKernel x y • cross (ω.val y) (x - y))
      NavierStokes3D.volume)
    (hH : KineticEnergyHamiltonian ω ≠ 0) : ¬ RegularStreamRepresentative ω := by
  rintro ⟨ψ, hrep, -⟩
  exact not_isGateauxRepresentative_kineticEnergy ω hω hloc hH ψ hrep.1

theorem curl_zero : curl (0 : VelocityField) = 0 := by
  funext x
  ext i
  fin_cases i <;> simp [curl, directionalCoord]

/-- **Refutation of `KineticEnergyCurlIdentityReg`** under the same hypotheses: the regular
derivative falls back to `0`, so the identity would force `u = 0`, contradicting `H(ω) ≠ 0`. -/
theorem not_kineticEnergyCurlIdentityReg (ω : CoadjointOrbit)
    (hω : ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (hloc : ∀ x, Integrable (fun y => biotSavartKernel x y • cross (ω.val y) (x - y))
      NavierStokes3D.volume)
    (hH : KineticEnergyHamiltonian ω ≠ 0) : ¬ KineticEnergyCurlIdentityReg ω := by
  intro hid
  have hnone : ¬ ∃ d, RegularRep KineticEnergyHamiltonian ω d :=
    fun ⟨d, hd⟩ => not_isGateauxRepresentative_kineticEnergy ω hω hloc hH d hd.1
  unfold KineticEnergyCurlIdentityReg RegularFunctionalDerivative at hid
  rw [dif_neg hnone, curl_zero] at hid
  apply hH
  unfold KineticEnergyHamiltonian
  rw [show BiotSavart ω.val = velocity_from_vorticity ω from rfl, ← hid]
  simp

end R3BiotSavart
