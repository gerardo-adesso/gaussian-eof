import Thm2Cert

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
