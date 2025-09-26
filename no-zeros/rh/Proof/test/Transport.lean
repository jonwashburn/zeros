import rh.RS.BoundaryAI
import rh.academic_framework.HalfPlaneOuterV2
import rh.RS.Cayley

/-!
Minimal smoke test: ensure the RS transport specialization elaborates for the
pinch field.
-/

-- RS transport predicate for the pinch field from a Poisson representation
#check RH.RS.transport_for_pinch_of_rep
-- New proof-layer transport helper
#check RH.Proof.Transport.hTrans_default
