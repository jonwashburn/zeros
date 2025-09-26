import rh.RS.PPlusFromCarleson
import rh.RS.OuterWitness
import rh.RS.Cayley
import rh.Cert.KxiPPlus

/-!
Minimal smoke test: ensure the Carleson→(P+) façade elaborates for the
concrete pinch field with `O_default`.
-/

-- The statement-level (P+) from Carleson existence, specialized to the pinch field
#check RH.Cert.PPlusFromCarleson_exists (fun z => (2 : ℂ) * RH.RS.J_pinch RH.RS.det2 RH.RS.O_default z)
-- New façade name
#check RH.RS.PPlusFromCarleson_exists_proved
