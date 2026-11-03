-- Axiom audit: prints the axioms of every theorem/lemma in the project.
-- CI fails unless each depends only on propext, Classical.choice, Quot.sound (or none).
import R3BiotSavartStream
import R3BiotSavartStream.Corrected
import R3BiotSavartStream.LocalIntegrability
import R3BiotSavartStream.Ported
import R3BiotSavartStream.Refutation

#print axioms R3BiotSavart.DivergenceFreeTestField.continuous
#print axioms R3BiotSavart.DivergenceFreeTestField.differentiable
#print axioms R3BiotSavart.DivergenceFreeTestField.integrable
#print axioms R3BiotSavart.biotSavart_add_smul
#print axioms R3BiotSavart.gateauxOn_unique
#print axioms R3BiotSavart.hasDerivAt_kineticEnergy
#print axioms R3BiotSavart.integral_norm_add_smul_sq
#print axioms R3BiotSavart.kineticEnergyCurlIdentityOn
#print axioms R3BiotSavart.kineticEnergy_add_smul
#print axioms R3BiotSavart.not_kineticEnergyCurlIdentityReg_of_divergenceFreeTestField
#print axioms R3BiotSavart.not_regularStreamRepresentative_of_divergenceFreeTestField
#print axioms R3BiotSavart.streamRepresentative
#print axioms R3BiotSavart.continuous_cross
#print axioms R3BiotSavart.integrable_biotSavart_integrand
#print axioms R3BiotSavart.integrable_indicator_ball_rpow_neg_two
#print axioms R3BiotSavart.measurable_kernelProfile
#print axioms R3BiotSavart.norm_cross_le
#print axioms ArnoldGeometric.CoadjointOrbit.property
#print axioms ArnoldGeometric.divergenceFree_iff
#print axioms ArnoldGeometric.gateaux_representative_unique
#print axioms ArnoldGeometric.orbit_add_smul_div_free
#print axioms FrohmanianTether.RegularField.cont
#print axioms FrohmanianTether.RegularField.diff
#print axioms FrohmanianTether.RegularField.div_free
#print axioms FrohmanianTether.RegularField.memL2
#print axioms FrohmanianTether.kineticEnergyCurlIdentityReg_of_regularStream
#print axioms FrohmanianTether.pairing_integrable
#print axioms FrohmanianTether.regularField_sub
#print axioms FrohmanianTether.regularFunctionalDerivative_eq
#print axioms FrohmanianTether.regularRep_unique
#print axioms NavierStokes3D.div_add
#print axioms NavierStokes3D.div_add_smul
#print axioms NavierStokes3D.div_const
#print axioms NavierStokes3D.div_smul
#print axioms NavierStokes3D.eq_of_l2_energy_zero
#print axioms NavierStokes3D.smul_coord
#print axioms ArnoldGeometric.CoadjointOrbit.mk.congr_simp
#print axioms R3BiotSavart.biotSavartKernel_eq_profile
#print axioms R3BiotSavart.biotSavartKernel_of_ne'
#print axioms R3BiotSavart.cross_add_smul
#print axioms R3BiotSavart.curl_zero
#print axioms R3BiotSavart.exists_const_not_integrable
#print axioms R3BiotSavart.norm_le_sum_norm_cross
#print axioms R3BiotSavart.norm_sq_cross_single
#print axioms R3BiotSavart.not_integrable_norm_rpow_neg_two
#print axioms R3BiotSavart.not_isGateauxRepresentative_kineticEnergy
#print axioms R3BiotSavart.not_kineticEnergyCurlIdentityReg
#print axioms R3BiotSavart.not_regularStreamRepresentative
#print axioms R3BiotSavart.orbit_zero_smul
