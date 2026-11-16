# Kernel certificate: r3-biot-savart-stream

This file records a reproducible machine check of the Lean 4 development in this repository. Lean does not issue a signed "official" certificate. What is recorded here is the exact commit and toolchain, the complete `lake build` log, a scan for `sorry`/`admit`/`native_decide`/`axiom`, the `#print axioms` result for every theorem the build produces, and a replay of every module through Lean's kernel with the toolchain's `leanchecker`. Each check can be rerun with the command at the end.

| Item | Value |
|---|---|
| Repository | https://github.com/BenFrohman/r3-biot-savart-stream |
| Certified commit | `a82327118aac34897bd453d013b7d0b67f34437c` (branch `chore/kernel-certificate`) |
| Lean sources | identical to `main` at `28d3afb5e4a541746cc1f1b02f0d92ab83d5eea2`: no `.lean`, lakefile, manifest or toolchain file differs; the certified commit only adds CI and the scripts in `certificates/tools/` |
| lean-toolchain | `leanprover/lean4:v4.30.0-rc1` |
| Lean | Lean (version 4.30.0-rc1, x86_64-unknown-linux-gnu, commit 714601baf118066cbf3f282361339c6d06665b2a, Release) |
| Mathlib | `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7` (lake-manifest.json; inputRev `v4.30.0-rc1`) |
| Date (UTC) | 2026-11-16T19:18:18Z |
| CI run | https://github.com/BenFrohman/r3-biot-savart-stream/actions/runs/43937843288 |
| `lake build` | `Build completed successfully (8269 jobs).` ([build.log](build.log)) |
| sorry / admit / native_decide / axiom scan | `RESULT: 0 hits` ([sorry-scan.txt](sorry-scan.txt)) |
| `#print axioms` | `AUDIT PASS: 62 theorems in 4 modules depend only on propext, Classical.choice, Quot.sound (or on no axioms)` ([axioms.txt](axioms.txt)) |
| Kernel replay (leanchecker) | `RESULT: 5 of 5 modules replayed through the kernel, 0 failures` ([leanchecker.txt](leanchecker.txt)) |

## What each check means

- **Build.** `lake build` of the default targets with the pinned toolchain. Mathlib comes from `lake exe cache get` (it is never rebuilt from source). The build elaborates every proof and sends each declaration to Lean's kernel.
- **Scan.** `certificates/tools/sorry_scan.py` strips comments and strings from every tracked `.lean` file and reports any `sorry`, `admit`, `native_decide` or `axiom` declaration. Result: RESULT: 0 hits.
- **Axioms.** `certificates/tools/gen_audit.py` imports all 5 built modules ([modules.txt](modules.txt)) and calls `Lean.collectAxioms`, the function behind `#print axioms`, on every theorem declared in them (62 theorems, auto-generated internal names excluded). `check_audit.py` fails unless each depends only on `propext`, `Classical.choice` and `Quot.sound`, or on no axioms. Raw output: [axioms.raw.txt](axioms.raw.txt); generated Lean file: [KernelCertificateAudit.lean.txt](KernelCertificateAudit.lean.txt).
- **Kernel replay.** checker: leanchecker source shipped with v4.30.0-rc1 (src/lean/LeanChecker.lean), prefix match -> exact match, run with lean --run. For each module, the checker loads the module's imports from their `.olean` files and replays every declaration of that module through the kernel. The stock checker treats its argument as a module-name prefix and replays all matching modules in parallel, which runs out of memory on a root module, so it is run once per module with exact matching (the one-line patch is printed in [leanchecker.txt](leanchecker.txt)). The checker's own documentation describes it as a tool to detect environment hacking, not an independent external verifier; imported Mathlib and core declarations are trusted from their `.olean` files.

## Scope

The axiom result says the listed theorems are proved from Lean's standard axioms. It does not by itself say what the theorems mean; read the statements in the sources. Conditional theorems remain conditional on their hypotheses.

Full `#print axioms` output (verbatim from `axioms.txt`):

```
'R3BiotSavart.DivergenceFreeTestField.continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.DivergenceFreeTestField.differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.DivergenceFreeTestField.integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.RegularDerivativeOn.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.biotSavart_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.gateauxOn_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.hasDerivAt_kineticEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.integral_norm_add_smul_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.kineticEnergyCurlIdentityOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.kineticEnergy_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.not_kineticEnergyCurlIdentityReg_of_divergenceFreeTestField' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.not_regularStreamRepresentative_of_divergenceFreeTestField' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.streamRepresentative' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.continuous_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.integrable_biotSavart_integrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.integrable_indicator_ball_rpow_neg_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.measurable_kernelProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.norm_cross_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointOrbit.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointOrbit.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointOrbit.mk.sizeOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointOrbit.property' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.divergenceFree_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.gateaux_representative_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.orbit_add_smul_div_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.pairing.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.RegularField.cont' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.RegularField.diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.RegularField.div_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.RegularField.memL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.RegularFunctionalDerivative.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.kineticEnergyCurlIdentityReg_of_regularStream' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.pairing_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.regularField_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.regularFunctionalDerivative_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'FrohmanianTether.regularRep_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.div_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.div_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.div_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.div_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.eq_of_l2_energy_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.smul_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.volume.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.CoadjointOrbit.mk.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.KineticEnergyHamiltonian.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.biotSavartKernel.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArnoldGeometric.cross.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.curl.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NavierStokes3D.directionalCoord.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.biotSavartKernel_eq_profile' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.biotSavartKernel_of_ne'' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.cross_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.curl_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.exists_const_not_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.kernelProfile.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.norm_le_sum_norm_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.norm_sq_cross_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.not_integrable_norm_rpow_neg_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.not_isGateauxRepresentative_kineticEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.not_kineticEnergyCurlIdentityReg' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.not_regularStreamRepresentative' depends on axioms: [propext, Classical.choice, Quot.sound]
'R3BiotSavart.orbit_zero_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Rebuild

```
git clone https://github.com/BenFrohman/r3-biot-savart-stream.git && cd r3-biot-savart-stream && git checkout a82327118aac34897bd453d013b7d0b67f34437c && lake exe cache get && lake build && python3 certificates/tools/sorry_scan.py && python3 certificates/tools/gen_audit.py /tmp/KernelCertificateAudit.lean /tmp/modules.txt && lake env lean /tmp/KernelCertificateAudit.lean > /tmp/axioms.raw.txt && python3 certificates/tools/check_audit.py /tmp/axioms.raw.txt | tail -n 1
```
