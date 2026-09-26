import AutomataCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0

namespace CloitreCollaboration.Certificate.Operations

def OneRows : Array (Array Nat) := #[#[0,1],#[2,2],#[2,2]]
def OneFinal : Array Bool := #[false,true,false]
def OneTransitions : Lookup Nat := (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 2) (.leaf 2))))
def OneAcceptance : Lookup Bool := (.node (.node (.leaf false) (.leaf false)) (.node (.leaf true) (.leaf false)))
def One : Machine 2 3 where
  start := ⟨0, by decide⟩
  step q c := Fin.ofNat 3 (OneTransitions.get (q.val * 2 + c.val))
  accept q := OneAcceptance.get q.val


end CloitreCollaboration.Certificate.Operations
