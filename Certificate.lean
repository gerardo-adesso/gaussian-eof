import Thm2Cert
import Thm1Cert

/-! Axiom audit: every certified statement depends only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). -/

-- Lemma S5: positivity and kernel
#print axioms Thm2Cert.lemmaS5_psd
#print axioms Thm2Cert.lemmaS5_pd
#print axioms Thm2Cert.lemmaS5_kernel
#print axioms Thm2Cert.lemmaS5_null
#print axioms Thm2Cert.lemmaS5_complex
#print axioms Thm2Cert.lemmaS5_complex_pd
#print axioms Thm2Cert.lemmaS5_complex_kernel
#print axioms Thm2Cert.hyp_nonvacuous
-- Lemma S5: comparison M ≥ γK with explicit γ
#print axioms Thm2Cert.gam_pos
#print axioms Thm2Cert.lemmaS5_gamma
#print axioms Thm2Cert.lemmaS5_gamma_complex
-- Eqs. (S:defects), (S:Q12), (S:mainid)
#print axioms Thm2Cert.defects
#print axioms Thm2Cert.Q1_from_euler
#print axioms Thm2Cert.Q2_from_euler
#print axioms Thm2Cert.mainid
#print axioms Thm2Cert.mainid_general
-- Rigidity
#print axioms Thm2Cert.rigidity
#print axioms Thm2Cert.rigidity_multi
#print axioms Thm2Cert.stationary_rigidity
-- Reduction to Theorem 2
#print axioms Thm2Cert.calib_iff
#print axioms Thm2Cert.lam_pos
#print axioms Thm2Cert.hyp_of_lam
#print axioms Thm2Cert.tmsv_value
#print axioms Thm2Cert.energy_identity
#print axioms Thm2Cert.thm2_of_minprinciple
-- Theorem 1: defect inequality (Theorem S1)
#print axioms Thm1Cert.drop_lemma
#print axioms Thm1Cert.pointwise
#print axioms Thm1Cert.defect_inequality_tsum
-- Theorem 1: compression (Theorem S2)
#print axioms Thm1Cert.pava_exists
#print axioms Thm1Cert.entropy_le_of_prefix
#print axioms Thm1Cert.compression
-- Theorem 1: thermal closure
#print axioms Thm1Cert.H_thermal
#print axioms Thm1Cert.F_thermal
#print axioms Thm1Cert.support
#print axioms Thm1Cert.Fmoments
#print axioms Thm1Cert.brk_of_upsilon
-- Theorem 1: assembly and corollaries
#print axioms Thm1Cert.thm1_spectrum
#print axioms Thm1Cert.theorem1
#print axioms Thm1Cert.theorem1_upsilon
#print axioms Thm1Cert.theorem1_limit
#print axioms Thm1Cert.entropy_truncation
#print axioms Thm1Cert.theorem1_endpoint_state
#print axioms Thm1Cert.fixed_entanglement
#print axioms Thm1Cert.fixed_entanglement_endpoint
#print axioms Thm1Cert.separability_criterion
