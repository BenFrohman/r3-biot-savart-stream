/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman.

# Corrected stream-function representative on ℝ³

Function class: `ω` smooth (`ContDiff ℝ ∞`), compactly supported, divergence-free.
Test directions: smooth, compactly supported, divergence-free `ε`.
-/
import R3BiotSavartStream.LocalIntegrability

open MeasureTheory Filter Topology

namespace R3BiotSavart

open NavierStokes3D ArnoldGeometric FrohmanianTether

/-- Smooth compactly supported divergence-free fields (the function class and the test class). -/
def TestDirection (ε : CoadjointOrbit) : Prop :=
  ContDiff ℝ ⊤ ε.val ∧ HasCompactSupport ε.val

theorem TestDirection.differentiable {ε : CoadjointOrbit} (h : TestDirection ε) :
    ∀ i x, DifferentiableAt ℝ (fun y => ε.val y i) x := fun i x =>
  ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).differentiableAt).comp x
    (h.1.differentiable (by simp) x)

theorem TestDirection.continuous {ε : CoadjointOrbit} (h : TestDirection ε) :
    Continuous ε.val := h.1.continuous

theorem TestDirection.integrable {ε : CoadjointOrbit} (h : TestDirection ε) (x : T3) :
    Integrable (fun y => biotSavartKernel x y • cross (ε.val y) (x - y)) NavierStokes3D.volume :=
  integrable_biotSavart_integrand h.continuous h.2 x

/-- **Class-level refutation.** For every smooth compactly supported divergence-free `ω` with
nonzero kinetic energy, the tether's `RegularStreamRepresentative ω` is false. -/
theorem not_regularStreamRepresentative_of_testDirection {ω : CoadjointOrbit}
    (hω : TestDirection ω) (hH : KineticEnergyHamiltonian ω ≠ 0) :
    ¬ RegularStreamRepresentative ω :=
  not_regularStreamRepresentative ω hω.differentiable hω.integrable hH

theorem not_kineticEnergyCurlIdentityReg_of_testDirection {ω : CoadjointOrbit}
    (hω : TestDirection ω) (hH : KineticEnergyHamiltonian ω ≠ 0) :
    ¬ KineticEnergyCurlIdentityReg ω :=
  not_kineticEnergyCurlIdentityReg ω hω.differentiable hω.integrable hH

/-- Gâteaux representative tested only against `TestDirection`s. -/
def IsGateauxRepresentativeOn (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit)
    (δ : T3 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ (ε : CoadjointOrbit) (_ : TestDirection ε)
    (hω : ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (hε : ∀ i x, DifferentiableAt ℝ (fun y => ε.val y i) x),
    HasDerivAt (fun t : ℝ =>
      F ⟨fun x => ω.val x + t • ε.val x,
        fun x => orbit_add_smul_div_free ω ε t hω hε x⟩)
      (∫ x, pairing (δ x) (ε.val x) ∂volume) 0

/-! ### Linearity and the exact Gâteaux expansion -/

theorem biotSavart_add_smul {f g : T3 → EuclideanSpace ℝ (Fin 3)} (t : ℝ) (x : T3)
    (hf : Integrable (fun y => biotSavartKernel x y • cross (f y) (x - y)) NavierStokes3D.volume)
    (hg : Integrable (fun y => biotSavartKernel x y • cross (g y) (x - y)) NavierStokes3D.volume) :
    BiotSavart (fun y => f y + t • g y) x = BiotSavart f x + t • BiotSavart g x := by
  unfold BiotSavart
  have : (fun y => biotSavartKernel x y • cross (f y + t • g y) (x - y)) =
      fun y => biotSavartKernel x y • cross (f y) (x - y) +
        t • (biotSavartKernel x y • cross (g y) (x - y)) := by
    funext y; rw [cross_add_smul, smul_add, smul_comm]
  have hg' : Integrable (fun y => t • (biotSavartKernel x y • cross (g y) (x - y)))
      NavierStokes3D.volume := hg.smul t
  rw [this, integral_add hf hg', integral_smul]

theorem integral_norm_add_smul_sq {a b : T3 → EuclideanSpace ℝ (Fin 3)}
    (ha : MemLp a 2 NavierStokes3D.volume) (hb : MemLp b 2 NavierStokes3D.volume) (t : ℝ) :
    ∫ x, ‖a x + t • b x‖ ^ 2 ∂volume =
      (∫ x, ‖a x‖ ^ 2 ∂volume) + 2 * t * (∫ x, pairing (a x) (b x) ∂volume) +
        t ^ 2 * ∫ x, ‖b x‖ ^ 2 ∂volume := by
  have hA : Integrable (fun x => ‖a x‖ ^ 2) NavierStokes3D.volume :=
    ha.integrable_norm_pow (by norm_num)
  have hB : Integrable (fun x => ‖b x‖ ^ 2) NavierStokes3D.volume :=
    hb.integrable_norm_pow (by norm_num)
  have hP := pairing_integrable ha hb
  have hpt : (fun x => ‖a x + t • b x‖ ^ 2) = fun x =>
      (‖a x‖ ^ 2 + (2 * t) * pairing (a x) (b x)) + t ^ 2 * ‖b x‖ ^ 2 := by
    funext x
    rw [norm_add_sq_real, norm_smul, inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs, pairing]
    ring
  have hP' : Integrable (fun x => (2 * t) * pairing (a x) (b x)) NavierStokes3D.volume :=
    hP.const_mul _
  have hB' : Integrable (fun x => t ^ 2 * ‖b x‖ ^ 2) NavierStokes3D.volume := hB.const_mul _
  have hAP : Integrable (fun x => ‖a x‖ ^ 2 + (2 * t) * pairing (a x) (b x))
      NavierStokes3D.volume := hA.add hP'
  rw [hpt, integral_add hAP hB', integral_add hA hP', integral_const_mul, integral_const_mul]

/-- Velocity of a test direction lies in `L²` (classical: `BS ε = O(|x|⁻²)` at infinity). -/
def TestVelocityL2 : Prop :=
  ∀ ε : CoadjointOrbit, TestDirection ε → MemLp (BiotSavart ε.val) 2 NavierStokes3D.volume

/-- **Proved expansion.** `H(ω + tε) = H ω + t ∫⟨BSω, BSε⟩ + (t²/2)‖BSε‖²`. -/
theorem kineticEnergy_add_smul {ω ε : CoadjointOrbit} (hω : TestDirection ω)
    (hε : TestDirection ε) (hL2 : TestVelocityL2) (t : ℝ) (p) :
    KineticEnergyHamiltonian ⟨fun x => ω.val x + t • ε.val x, p⟩ =
      KineticEnergyHamiltonian ω +
        t * (∫ x, pairing (BiotSavart ω.val x) (BiotSavart ε.val x) ∂volume) +
        t ^ 2 * ((1 / 2) * ∫ x, ‖BiotSavart ε.val x‖ ^ 2 ∂volume) := by
  unfold KineticEnergyHamiltonian
  have hfun : BiotSavart (fun x => ω.val x + t • ε.val x) =
      fun x => BiotSavart ω.val x + t • BiotSavart ε.val x := by
    funext x; exact biotSavart_add_smul t x (hω.integrable x) (hε.integrable x)
  simp only
  rw [hfun, integral_norm_add_smul_sq (hL2 ω hω) (hL2 ε hε)]
  ring

theorem hasDerivAt_kineticEnergy {ω ε : CoadjointOrbit} (hω : TestDirection ω)
    (hε : TestDirection ε) (hL2 : TestVelocityL2)
    (hωd : ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (hεd : ∀ i x, DifferentiableAt ℝ (fun y => ε.val y i) x) :
    HasDerivAt (fun t : ℝ => KineticEnergyHamiltonian
      ⟨fun x => ω.val x + t • ε.val x, fun x => orbit_add_smul_div_free ω ε t hωd hεd x⟩)
      (∫ x, pairing (BiotSavart ω.val x) (BiotSavart ε.val x) ∂volume) 0 := by
  set B := ∫ x, pairing (BiotSavart ω.val x) (BiotSavart ε.val x) ∂volume
  set C := (1 / 2) * ∫ x, ‖BiotSavart ε.val x‖ ^ 2 ∂volume
  have hfun : (fun t : ℝ => KineticEnergyHamiltonian
      ⟨fun x => ω.val x + t • ε.val x, fun x => orbit_add_smul_div_free ω ε t hωd hεd x⟩) =
      fun t => KineticEnergyHamiltonian ω + t * B + t ^ 2 * C := by
    funext t; exact kineticEnergy_add_smul hω hε hL2 t _
  rw [hfun]
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const B).const_add (KineticEnergyHamiltonian ω)).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const C)
  convert h using 1
  simp

/-! ### Named analytic inputs (not proved here) -/

/-- **Newtonian stream facts** for `ω`: there is a regular `ψ` (classically `ψ = (-Δ)⁻¹ω`) with
`curl ψ = BS ω`, `BS ω ∈ L²`, and the integration by parts with decay at infinity
`∫⟨BSω, BSε⟩ = ∫⟨ψ, ε⟩` for every test direction `ε`. -/
def NewtonianStreamFacts (ω : CoadjointOrbit) : Prop :=
  ∃ ψ : T3 → EuclideanSpace ℝ (Fin 3), RegularField ψ ∧ curl ψ = BiotSavart ω.val ∧
    ∀ ε : CoadjointOrbit, TestDirection ε →
      ∫ x, pairing (BiotSavart ω.val x) (BiotSavart ε.val x) ∂volume =
        ∫ x, pairing (ψ x) (ε.val x) ∂volume

/-- **L² div-free Liouville / de Rham**: a regular field orthogonal to all test directions is 0. -/
def L2DivFreeLiouville : Prop :=
  ∀ w : T3 → EuclideanSpace ℝ (Fin 3), RegularField w →
    (∀ ε : CoadjointOrbit, TestDirection ε → ∫ x, pairing (w x) (ε.val x) ∂volume = 0) → w = 0

/-! ### Main conditional theorems -/

/-- **Stream representative (corrected).** -/
theorem streamRepresentative {ω : CoadjointOrbit} (hω : TestDirection ω)
    (hL2 : TestVelocityL2) (hN : NewtonianStreamFacts ω) :
    ∃ ψ, RegularField ψ ∧ IsGateauxRepresentativeOn KineticEnergyHamiltonian ω ψ ∧
      curl ψ = BiotSavart ω.val ∧
      KineticEnergyHamiltonian ω = (1 / 2) * ∫ x, pairing (ψ x) (ω.val x) ∂volume := by
  obtain ⟨ψ, hreg, hcurl, hibp⟩ := hN
  refine ⟨ψ, hreg, fun ε hε hωd hεd => ?_, hcurl, ?_⟩
  · rw [← hibp ε hε]; exact hasDerivAt_kineticEnergy hω hε hL2 hωd hεd
  · rw [← hibp ω hω, KineticEnergyHamiltonian]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [pairing]

theorem gateauxOn_unique (hLiou : L2DivFreeLiouville) {F : CoadjointOrbit → ℝ}
    {ω : CoadjointOrbit} (hωd : ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    {d d' : T3 → EuclideanSpace ℝ (Fin 3)}
    (h : IsGateauxRepresentativeOn F ω d) (hr : RegularField d)
    (h' : IsGateauxRepresentativeOn F ω d') (hr' : RegularField d') : d = d' := by
  have hw := regularField_sub hr hr'
  have h0 := hLiou _ hw fun ε hε => by
    have hεd := hε.differentiable
    have heq := (h ε hε hωd hεd).unique (h' ε hε hωd hεd)
    have hεL2 : MemLp ε.val 2 NavierStokes3D.volume :=
      hε.continuous.memLp_of_hasCompactSupport (μ := MeasureTheory.volume) hε.2
    have hsub : (fun x => pairing (d x - d' x) (ε.val x)) =
        fun x => pairing (d x) (ε.val x) - pairing (d' x) (ε.val x) := by
      funext x; simp [pairing, inner_sub_left]
    rw [hsub, integral_sub (pairing_integrable hr.memL2 hεL2)
      (pairing_integrable hr'.memL2 hεL2), heq, sub_self]
  funext x; simpa [sub_eq_zero] using congrFun h0 x

open Classical in
noncomputable def RegularDerivativeOn (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit) :
    T3 → EuclideanSpace ℝ (Fin 3) :=
  if h : ∃ d, IsGateauxRepresentativeOn F ω d ∧ RegularField d then Classical.choose h else 0

def KineticEnergyCurlIdentityOn (ω : CoadjointOrbit) : Prop :=
  curl (RegularDerivativeOn KineticEnergyHamiltonian ω) = velocity_from_vorticity ω

/-- **Corrected curl identity**: `curl (δH/δω) = u` with derivatives tested on `TestDirection`s. -/
theorem kineticEnergyCurlIdentityOn {ω : CoadjointOrbit} (hω : TestDirection ω)
    (hL2 : TestVelocityL2) (hN : NewtonianStreamFacts ω) (hLiou : L2DivFreeLiouville) :
    KineticEnergyCurlIdentityOn ω := by
  obtain ⟨ψ, hreg, hrep, hcurl, -⟩ := streamRepresentative hω hL2 hN
  have hex : ∃ d, IsGateauxRepresentativeOn KineticEnergyHamiltonian ω d ∧ RegularField d :=
    ⟨ψ, hrep, hreg⟩
  have hspec := Classical.choose_spec hex
  have : RegularDerivativeOn KineticEnergyHamiltonian ω = ψ := by
    rw [RegularDerivativeOn, dif_pos hex]
    exact gateauxOn_unique hLiou hω.differentiable hspec.1 hspec.2 hrep hreg
  unfold KineticEnergyCurlIdentityOn velocity_from_vorticity
  rw [this, hcurl]

end R3BiotSavart
