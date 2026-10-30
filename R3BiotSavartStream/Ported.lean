/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman.

# Definitions ported verbatim from `BenFrohman/frohmanian-symplectic-tether-regularity`
(commit `81357f6`: `NS_Equations.lean`, `ArnoldGeometric.lean`, `GateauxRepresentative.lean`).
Module keywords (`public`, `@[expose]`) are dropped; statements and bodies are unchanged.
-/
import Mathlib

open MeasureTheory

namespace NavierStokes3D

abbrev T3 : Type := EuclideanSpace ℝ (Fin 3)
abbrev VelocityField := T3 → EuclideanSpace ℝ (Fin 3)

noncomputable section

def volume : Measure T3 := MeasureTheory.volume

def directionalCoord (u : VelocityField) (comp dir : Fin 3) (x : T3) : ℝ :=
  (fderiv ℝ (fun y => u y comp) x) (EuclideanSpace.single dir 1)

def div (u : VelocityField) (x : T3) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ (fun y => u y i) x) (EuclideanSpace.single i 1)

theorem smul_coord (c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    (c • v) i = c * v i := by
  rw [PiLp.smul_apply, smul_eq_mul]

theorem div_smul (c : ℝ) (u : VelocityField) (x : T3) :
    div (fun y => c • u y) x = c * div u x := by
  unfold div
  have hfun : ∀ i : Fin 3,
      (fun y => (c • u y) i) = c • fun y => u y i := by
    intro i
    funext y
    exact smul_coord c (u y) i
  calc
    ∑ i : Fin 3, (fderiv ℝ (fun y => (c • u y) i) x) (EuclideanSpace.single i 1)
        = ∑ i : Fin 3, (fderiv ℝ (c • fun y => u y i) x) (EuclideanSpace.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hfun i]
    _ = ∑ i : Fin 3, (c • fderiv ℝ (fun y => u y i) x) (EuclideanSpace.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [fderiv_const_smul_field, Pi.smul_apply]
    _ = ∑ i : Fin 3, c * (fderiv ℝ (fun y => u y i) x) (EuclideanSpace.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    _ = c * ∑ i : Fin 3, (fderiv ℝ (fun y => u y i) x) (EuclideanSpace.single i 1) := by
          rw [← Finset.mul_sum]

theorem div_add (u v : VelocityField) (x : T3)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u y i) x)
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) :
    div (fun y => u y + v y) x = div u x + div v x := by
  unfold div
  have hfun : ∀ i : Fin 3,
      (fun y => (u y + v y) i) = fun y => u y i + v y i := by
    intro i
    funext y
    rw [PiLp.add_apply]
  calc
    ∑ i : Fin 3, (fderiv ℝ (fun y => (u y + v y) i) x) (EuclideanSpace.single i 1)
        = ∑ i : Fin 3, (fderiv ℝ (fun y => u y i + v y i) x) (EuclideanSpace.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hfun i]
    _ = ∑ i : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) + (fderiv ℝ (fun y => v y i) x))
            (EuclideanSpace.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [fderiv_fun_add (hu i) (hv i)]
    _ = ∑ i : Fin 3, (fderiv ℝ (fun y => u y i) x) (EuclideanSpace.single i 1) +
        ∑ i : Fin 3, (fderiv ℝ (fun y => v y i) x) (EuclideanSpace.single i 1) := by
          simp only [ContinuousLinearMap.add_apply, Finset.sum_add_distrib]

theorem div_add_smul (u v : VelocityField) (c : ℝ) (x : T3)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u y i) x)
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) :
    div (fun y => u y + c • v y) x = div u x + c * div v x := by
  have hcv : ∀ i, DifferentiableAt ℝ (fun y => (c • v y) i) x := by
    intro i
    have hfun : (fun y => (c • v y) i) = c • fun y => v y i := by
      funext y
      exact smul_coord c (v y) i
    rw [hfun]
    exact (hv i).const_smul c
  have hadd :=
    div_add u (fun y => c • v y) x hu hcv
  rw [hadd, div_smul]

theorem div_const (v : EuclideanSpace ℝ (Fin 3)) (x : T3) :
    div (fun _ => v) x = 0 := by
  unfold div
  simp

def curl (u : VelocityField) (x : T3) : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 0 (directionalCoord u 2 1 x - directionalCoord u 1 2 x) +
    EuclideanSpace.single 1 (directionalCoord u 0 2 x - directionalCoord u 2 0 x) +
    EuclideanSpace.single 2 (directionalCoord u 1 0 x - directionalCoord u 0 1 x)

theorem eq_of_l2_energy_zero
    (w : VelocityField)
    (hInt : Integrable (fun x : T3 => ‖w x‖ ^ 2))
    (hE : (∫ x, ‖w x‖ ^ 2 ∂volume) = 0)
    (hcont : Continuous w) :
    w = 0 := by
  have hnn : 0 ≤ fun x : T3 => ‖w x‖ ^ 2 := fun x => pow_nonneg (norm_nonneg _) _
  have hcontSq : Continuous fun x : T3 => ‖w x‖ ^ 2 :=
    (continuous_norm.comp hcont).pow 2
  by_contra hne
  have hx : ∃ x, w x ≠ 0 := by
    contrapose! hne
    funext x
    exact hne x
  obtain ⟨x, hx⟩ := hx
  have hx0 : (fun y => ‖w y‖ ^ 2) x ≠ 0 := by
    intro hsq
    exact hx (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  have hInt' : Integrable (fun y => ‖w y‖ ^ 2) MeasureTheory.volume := by
    simpa [volume] using hInt
  have hpos :=
    integral_pos_of_integrable_nonneg_nonzero (μ := MeasureTheory.volume)
      hcontSq hInt' hnn hx0
  have hE' : (∫ y, ‖w y‖ ^ 2 ∂MeasureTheory.volume) = 0 := by
    simpa [volume] using hE
  exact (not_lt_of_ge (le_of_eq hE')) hpos

end

end NavierStokes3D

namespace ArnoldGeometric

open NavierStokes3D

structure CoadjointOrbit where
  val : T3 → EuclideanSpace ℝ (Fin 3)
  property : ∀ x, NavierStokes3D.div val x = 0

open Matrix in
noncomputable def cross (u v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (WithLp.ofLp u ⨯₃ WithLp.ofLp v)

noncomputable def pairing (u v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  inner ℝ u v

theorem orbit_add_smul_div_free (ω ε : CoadjointOrbit) (t : ℝ)
    (hω : ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (hε : ∀ i x, DifferentiableAt ℝ (fun y => ε.val y i) x) (x : T3) :
    NavierStokes3D.div (fun y => ω.val y + t • ε.val y) x = 0 := by
  rw [div_add_smul ω.val ε.val t x (fun i => hω i x) (fun i => hε i x),
      ω.property x, ε.property x, mul_zero, add_zero]

def IsGateauxRepresentative (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit)
    (δ : T3 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ (ε : CoadjointOrbit)
    (hω : ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (hε : ∀ i x, DifferentiableAt ℝ (fun y => ε.val y i) x),
    HasDerivAt (fun t : ℝ =>
      F ⟨fun x => ω.val x + t • ε.val x,
        fun x => orbit_add_smul_div_free ω ε t hω hε x⟩)
      (∫ x, pairing (δ x) (ε.val x) ∂volume) 0

theorem gateaux_representative_unique
    {F : CoadjointOrbit → ℝ} {ω : CoadjointOrbit}
    (δ δ' : T3 → EuclideanSpace ℝ (Fin 3))
    (hδ : IsGateauxRepresentative F ω δ)
    (hδ' : IsGateauxRepresentative F ω δ')
    (hω : ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (hdiff : ∀ i x, DifferentiableAt ℝ (fun y => (δ y - δ' y) i) x)
    (hdiv : ∀ x, NavierStokes3D.div (fun y => δ y - δ' y) x = 0)
    (hInt : Integrable (fun x : T3 => ‖δ x - δ' x‖ ^ 2))
    (hcont : Continuous fun x => δ x - δ' x)
    (hIntδ : Integrable (fun x => pairing (δ x) (δ x - δ' x)))
    (hIntδ' : Integrable (fun x => pairing (δ' x) (δ x - δ' x))) :
    δ = δ' := by
  let w : T3 → EuclideanSpace ℝ (Fin 3) := fun x => δ x - δ' x
  let ε : CoadjointOrbit := ⟨w, hdiv⟩
  have h1 := hδ ε hω hdiff
  have h2 := hδ' ε hω hdiff
  have heq :
      (∫ x, pairing (δ x) (ε.val x) ∂volume) =
        ∫ x, pairing (δ' x) (ε.val x) ∂volume :=
    HasDerivAt.unique h1 h2
  have hpt :
      (fun x => pairing (δ x) (ε.val x) - pairing (δ' x) (ε.val x)) =
        fun x => ‖w x‖ ^ 2 := by
    funext x
    have hw : ε.val x = w x := rfl
    have hsub :
        pairing (δ x) (w x) - pairing (δ' x) (w x) =
          pairing (δ x - δ' x) (w x) := by
      simp [pairing, inner_sub_left]
    have hw' : δ x - δ' x = w x := rfl
    rw [hw, hsub, hw', pairing, real_inner_self_eq_norm_sq]
  have hsub := integral_sub (μ := volume) hIntδ hIntδ'
  have hE : (∫ x, ‖w x‖ ^ 2 ∂volume) = 0 := by
    rw [← hpt]
    have hinter :
        (∫ x, pairing (δ x) (ε.val x) - pairing (δ' x) (ε.val x) ∂volume) =
          ∫ x, pairing (δ x) (δ x - δ' x) -
            pairing (δ' x) (δ x - δ' x) ∂volume := rfl
    rw [hinter, hsub]
    have hL : (∫ x, pairing (δ x) (δ x - δ' x) ∂volume) =
        ∫ x, pairing (δ x) (ε.val x) ∂volume := rfl
    have hR : (∫ x, pairing (δ' x) (δ x - δ' x) ∂volume) =
        ∫ x, pairing (δ' x) (ε.val x) ∂volume := rfl
    rw [hL, hR, heq, sub_self]
  have hw0 := eq_of_l2_energy_zero w hInt hE hcont
  funext x
  have hx := congrFun hw0 x
  simpa [w, sub_eq_zero] using hx

/-- Euclidean Biot–Savart kernel (principal-value: zero on the diagonal). -/
noncomputable def biotSavartKernel (x y : T3) : ℝ :=
  if x = y then 0 else (4 * Real.pi)⁻¹ * ‖x - y‖ ^ (-(3 : ℝ))

noncomputable def BiotSavart (ω : T3 → EuclideanSpace ℝ (Fin 3)) :
    T3 → EuclideanSpace ℝ (Fin 3) :=
  fun x => ∫ y, biotSavartKernel x y • cross (ω y) (x - y) ∂volume

noncomputable def KineticEnergyHamiltonian (ω : CoadjointOrbit) : ℝ :=
  (1/2) * ∫ x, ‖BiotSavart ω.val x‖^2 ∂(volume)

noncomputable def velocity_from_vorticity (ω : CoadjointOrbit) :
    T3 → EuclideanSpace ℝ (Fin 3) :=
  BiotSavart ω.val

end ArnoldGeometric

namespace FrohmanianTether

open MeasureTheory ArnoldGeometric NavierStokes3D

structure RegularField (d : T3 → EuclideanSpace ℝ (Fin 3)) : Prop where
  cont : Continuous d
  diff : ∀ i x, DifferentiableAt ℝ (fun y => d y i) x
  div_free : ∀ x, NavierStokes3D.div d x = 0
  memL2 : MemLp d 2 NavierStokes3D.volume

def RegularRep (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit)
    (d : T3 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  IsGateauxRepresentative F ω d ∧ RegularField d

theorem regularField_sub {d d' : T3 → EuclideanSpace ℝ (Fin 3)}
    (h : RegularField d) (h' : RegularField d') : RegularField (fun x => d x - d' x) where
  cont := h.cont.sub h'.cont
  diff := fun i x => by
    have := (h.diff i x).sub (h'.diff i x)
    simpa using this
  div_free := fun x => by
    have := div_add_smul d d' (-1) x (fun i => h.diff i x) (fun i => h'.diff i x)
    simp only [neg_one_smul, ← sub_eq_add_neg, h.div_free x, h'.div_free x] at this
    simpa using this
  memL2 := h.memL2.sub h'.memL2

theorem pairing_integrable {f g : T3 → EuclideanSpace ℝ (Fin 3)}
    (hf : MemLp f 2 NavierStokes3D.volume) (hg : MemLp g 2 NavierStokes3D.volume) :
    Integrable (fun x => pairing (f x) (g x)) NavierStokes3D.volume := by
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x h1 h2
  simp only [pairing, h1, h2]

theorem regularRep_unique {F : CoadjointOrbit → ℝ} {ω : CoadjointOrbit}
    (hω : ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    {d d' : T3 → EuclideanSpace ℝ (Fin 3)} (h : RegularRep F ω d) (h' : RegularRep F ω d') :
    d = d' := by
  have hw := regularField_sub h.2 h'.2
  refine gateaux_representative_unique d d' h.1 h'.1 hω hw.diff hw.div_free ?_ hw.cont ?_ ?_
  · simpa using hw.memL2.integrable_norm_pow (by norm_num)
  · exact pairing_integrable h.2.memL2 hw.memL2
  · exact pairing_integrable h'.2.memL2 hw.memL2

open Classical in
noncomputable def RegularFunctionalDerivative (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit) :
    T3 → EuclideanSpace ℝ (Fin 3) :=
  if h : ∃ d, RegularRep F ω d then Classical.choose h else 0

theorem regularFunctionalDerivative_eq {F : CoadjointOrbit → ℝ} {ω : CoadjointOrbit}
    (hω : ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    {d : T3 → EuclideanSpace ℝ (Fin 3)} (h : RegularRep F ω d) :
    RegularFunctionalDerivative F ω = d := by
  have hex : ∃ d, RegularRep F ω d := ⟨d, h⟩
  rw [RegularFunctionalDerivative, dif_pos hex]
  exact regularRep_unique hω (Classical.choose_spec hex) h

def KineticEnergyCurlIdentityReg (ω : CoadjointOrbit) : Prop :=
  curl (RegularFunctionalDerivative KineticEnergyHamiltonian ω) = velocity_from_vorticity ω

def RegularStreamRepresentative (ω : CoadjointOrbit) : Prop :=
  ∃ ψ, RegularRep KineticEnergyHamiltonian ω ψ ∧ curl ψ = velocity_from_vorticity ω

theorem kineticEnergyCurlIdentityReg_of_regularStream (ω : CoadjointOrbit)
    (hω : ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (h : RegularStreamRepresentative ω) : KineticEnergyCurlIdentityReg ω := by
  obtain ⟨ψ, hrep, hcurl⟩ := h
  unfold KineticEnergyCurlIdentityReg
  rw [regularFunctionalDerivative_eq hω hrep]
  exact hcurl

end FrohmanianTether
