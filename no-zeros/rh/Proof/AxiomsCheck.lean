import Lean
import rh.Proof.Export
import rh.Proof.CRClosure
import rh.Proof.Entry

-- Axiom check: print axioms used by the final RH export theorems.
#print axioms RH.Proof.Export.RiemannHypothesis_final
#print axioms RH.Proof.Export.RiemannHypothesis_from_certificate_route
#print axioms RH.Proof.Export.RiemannHypothesis_from_certificate_rep_on_via_cov

-- Additionally, check the core CR-outer wrapper.
#print axioms RH.Proof.Final.RiemannHypothesis_mathlib_from_CR_outer_ext

-- Public shims/entry points added in this repo
#print axioms RH.Proof.CRClosure.RH_from_CR_outer_choose
#print axioms RH.Proof.Entry.RiemannHypothesis_from_CR_outer


