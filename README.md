# r3-biot-savart-stream

[![Lean certificate](https://github.com/BenFrohman/r3-biot-savart-stream/actions/workflows/certify.yml/badge.svg)](https://github.com/BenFrohman/r3-biot-savart-stream/actions/workflows/certify.yml)

Lean 4 + Mathlib (v4.30.0-rc1). Setting: ℝ³ = `EuclideanSpace ℝ (Fin 3)` with Lebesgue measure.
It covers the stream-function fact ψ = (−Δ)⁻¹ω, u = curl ψ = BS ω, H = ½‖u‖² = ½⟨ω,ψ⟩
behind `RegularStreamRepresentative` in the tether development (commit 81357f6). The definitions
in `Ported.lean` are copied verbatim from there.

There is no `sorry` and there are no custom axioms. `AxiomAudit.lean` reports only `propext`,
`Classical.choice` and `Quot.sound`.

## 1. The original statement is false (proved, unconditional)

`IsGateauxRepresentative` tests against every differentiable divergence-free ε, and that
includes constant fields. The Biot–Savart integrand of a constant field is not integrable, so
its Bochner integral is 0. That forces H(ω) = 0.

- `not_regularStreamRepresentative_of_divergenceFreeTestField`: for every smooth, compactly supported,
  divergence-free ω with `KineticEnergyHamiltonian ω ≠ 0`, `¬ RegularStreamRepresentative ω`.
- `not_kineticEnergyCurlIdentityReg_of_divergenceFreeTestField`: in the same setting,
  `¬ KineticEnergyCurlIdentityReg ω`.
- The general forms are `not_regularStreamRepresentative` and
  `not_kineticEnergyCurlIdentityReg`. They take a differentiable ω whose BS integral converges
  at every point.
- `integrable_biotSavart_integrand` is proved: for continuous compactly supported f, the BS
  integrand is integrable at every x.

## 2. Corrected statement

The function class and the test class are the same: `DivergenceFreeTestField ω` means ω is `ContDiff ℝ ∞`,
compactly supported and divergence-free. The Gâteaux derivative (`IsGateauxRepresentativeOn`) is
tested only against `DivergenceFreeTestField`s.

Proved:
- `biotSavart_add_smul`: BS is linear.
- `kineticEnergy_add_smul`: the exact expansion
  H(ω+tε) = H(ω) + t∫⟨BSω,BSε⟩ + t²·½‖BSε‖².
- `hasDerivAt_kineticEnergy`: dH(ω)[ε] = ∫⟨BSω, BSε⟩.

These conditional results take the named Props in §3 as explicit hypotheses:
- `streamRepresentative` (needs `DivergenceFreeTestVelocityL2` and `VorticityStreamIntegrationByParts ω`): there is a ψ
  with `RegularField ψ`, ψ is a Gâteaux representative of H on DivergenceFree test fields, curl ψ = BS ω,
  and H(ω) = ½∫⟨ψ,ω⟩.
- `gateauxOn_unique` (needs `DivergenceFreeTestDense`): regular representatives are unique.
- `kineticEnergyCurlIdentityOn` (needs all three Props): curl(δH/δω) = u.

## 3. Named analytic hypotheses (not proved here)

- `DivergenceFreeTestVelocityL2`: BS ε ∈ L² for every DivergenceFree test field ε. Classically BS ε = O(|x|⁻²).
- `VorticityStreamIntegrationByParts ω`: ∃ ψ, `RegularField ψ` ∧ curl ψ = BS ω ∧ ∀ DivergenceFree test fields ε,
  ∫⟨BSω,BSε⟩ = ∫⟨ψ,ε⟩. This is the Newtonian potential plus integration by parts with decay.
- `DivergenceFreeTestDense`: a regular field that is L²-orthogonal to all DivergenceFree test fields is 0.

This repository does not address Navier–Stokes regularity.

## Copyright, license and scope

Copyright 2026 Benjamin Stanley Frohman (ORCID [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)). Licensed under the Apache License, Version 2.0; see `LICENSE` and `NOTICE`.

What is proved vs. conditional: Sections 1–2 are proved; Section 3 lists named analytic hypotheses that are not proved here. Every hypothesis is a named `Prop` passed as an explicit argument. Nothing in this repository claims to solve the Clay Millennium problem or global regularity for unmodified 3D Navier–Stokes.
