import Generated.SuccessorProduct

set_option maxRecDepth 1000000

set_option maxHeartbeats 0

namespace CloitreCollaboration.Certificate.Operations

def SuccessorRows : Array (Array Nat) := #[#[0,12,1,2],#[12,3,12,12],#[4,12,12,12],#[5,12,12,12],#[6,12,12,12],#[7,12,12,12],#[8,12,12,12],#[9,12,12,12],#[0,12,10,12],#[11,10,12,12],#[12,12,12,12],#[12,3,12,12],#[12,12,12,12]]
def SuccessorFinal : Array Bool := #[false,true,false,true,false,true,false,true,false,true,true,false,false]
def SuccessorTransitions : Lookup Nat := (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 6) (.leaf 12))) (.node (.node (.leaf 4) (.leaf 12)) (.node (.leaf 8) (.leaf 12)))) (.node (.node (.node (.leaf 12) (.leaf 11)) (.node (.leaf 7) (.leaf 12))) (.node (.node (.leaf 5) (.leaf 12)) (.node (.leaf 9) (.leaf 12))))) (.node (.node (.node (.node (.leaf 1) (.leaf 10)) (.node (.leaf 12) (.leaf 12))) (.node (.node (.leaf 12) (.leaf 12)) (.node (.leaf 12) (.leaf 12)))) (.node (.node (.node (.leaf 12) (.leaf 12)) (.node (.leaf 12) (.leaf 12))) (.node (.node (.leaf 12) (.leaf 12)) (.node (.leaf 12) (.leaf 12)))))) (.node (.node (.node (.node (.node (.leaf 12) (.leaf 12)) (.node (.leaf 12) (.leaf 12))) (.node (.node (.leaf 12) (.leaf 12)) (.node (.leaf 12) (.leaf 12)))) (.node (.node (.node (.leaf 3) (.leaf 10)) (.node (.leaf 12) (.leaf 12))) (.node (.node (.leaf 12) (.leaf 3)) (.node (.leaf 12) (.leaf 12))))) (.node (.node (.node (.node (.leaf 2) (.leaf 12)) (.node (.leaf 12) (.leaf 12))) (.node (.node (.leaf 12) (.leaf 12)) (.node (.leaf 12) (.leaf 12)))) (.node (.node (.node (.leaf 12) (.leaf 12)) (.node (.leaf 12) (.leaf 12))) (.node (.node (.leaf 12) (.leaf 12)) (.node (.leaf 12) (.leaf 12)))))))
def SuccessorAcceptance : Lookup Bool := (.node (.node (.node (.node (.leaf false) (.leaf false)) (.node (.leaf false) (.leaf false))) (.node (.node (.leaf false) (.leaf true)) (.node (.leaf false) (.leaf false)))) (.node (.node (.node (.leaf true) (.leaf true)) (.node (.leaf true) (.leaf false))) (.node (.node (.leaf true) (.leaf false)) (.node (.leaf true) (.leaf false)))))
def Successor : Machine 4 13 where
  start := ⟨0, by decide⟩
  step q c := Fin.ofNat 13 (SuccessorTransitions.get (q.val * 4 + c.val))
  accept q := SuccessorAcceptance.get q.val


def SuccessorRawRows : Array (Array Nat) := #[#[1,2,3,4],#[1,2,5,4],#[2,2,2,2],#[2,6,2,2],#[7,2,2,2],#[2,6,2,2],#[8,2,2,2],#[9,2,2,2],#[10,2,2,2],#[11,2,2,2],#[12,2,2,2],#[1,2,13,2],#[14,13,2,2],#[2,2,2,2],#[2,6,2,2],#[15,15,15,15]]
def SuccessorRawFinal : Array Bool := #[false,false,false,true,false,true,true,false,true,false,true,false,true,true,false,false]
def SuccessorRawTransitions : Lookup Nat := (.node (.node (.node (.node (.node (.node (.leaf 1) (.leaf 10)) (.node (.leaf 7) (.leaf 14))) (.node (.node (.leaf 2) (.leaf 12)) (.node (.leaf 8) (.leaf 2)))) (.node (.node (.node (.leaf 1) (.leaf 11)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 1)) (.node (.leaf 9) (.leaf 15))))) (.node (.node (.node (.node (.leaf 3) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2)))) (.node (.node (.node (.leaf 5) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 13)) (.node (.leaf 2) (.leaf 15)))))) (.node (.node (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 13))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 6)))) (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 6) (.leaf 2))) (.node (.node (.leaf 6) (.leaf 2)) (.node (.leaf 2) (.leaf 15))))) (.node (.node (.node (.node (.leaf 4) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2)))) (.node (.node (.node (.leaf 4) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 15)))))))
def SuccessorRawAcceptance : Lookup Bool := (.node (.node (.node (.node (.leaf false) (.leaf true)) (.node (.leaf false) (.leaf true))) (.node (.node (.leaf false) (.leaf true)) (.node (.leaf true) (.leaf false)))) (.node (.node (.node (.leaf false) (.leaf false)) (.node (.leaf true) (.leaf true))) (.node (.node (.leaf true) (.leaf false)) (.node (.leaf false) (.leaf false)))))
def SuccessorRaw : Machine 4 16 where
  start := ⟨0, by decide⟩
  step q c := Fin.ofNat 16 (SuccessorRawTransitions.get (q.val * 4 + c.val))
  accept q := SuccessorRawAcceptance.get q.val


def SuccessorSubsets : Array (List (Fin 12)) := #[[⟨0, by decide⟩],[⟨0, by decide⟩,⟨11, by decide⟩],[⟨11, by decide⟩],[⟨1, by decide⟩,⟨2, by decide⟩],[⟨3, by decide⟩,⟨11, by decide⟩],[⟨1, by decide⟩,⟨2, by decide⟩,⟨11, by decide⟩],[⟨2, by decide⟩,⟨4, by decide⟩,⟨11, by decide⟩],[⟨5, by decide⟩,⟨11, by decide⟩],[⟨2, by decide⟩,⟨6, by decide⟩,⟨11, by decide⟩],[⟨7, by decide⟩,⟨11, by decide⟩],[⟨2, by decide⟩,⟨8, by decide⟩,⟨11, by decide⟩],[⟨9, by decide⟩,⟨11, by decide⟩],[⟨2, by decide⟩,⟨10, by decide⟩,⟨11, by decide⟩],[⟨2, by decide⟩,⟨11, by decide⟩],[⟨1, by decide⟩,⟨11, by decide⟩],[]]

def SuccessorSubsetTree : Lookup (List (Fin 12)) := (.node (.node (.node (.node (.leaf [⟨0, by decide⟩]) (.leaf [⟨2, by decide⟩,⟨6, by decide⟩,⟨11, by decide⟩])) (.node (.leaf [⟨3, by decide⟩,⟨11, by decide⟩]) (.leaf [⟨2, by decide⟩,⟨10, by decide⟩,⟨11, by decide⟩]))) (.node (.node (.leaf [⟨11, by decide⟩]) (.leaf [⟨2, by decide⟩,⟨8, by decide⟩,⟨11, by decide⟩])) (.node (.leaf [⟨2, by decide⟩,⟨4, by decide⟩,⟨11, by decide⟩]) (.leaf [⟨1, by decide⟩,⟨11, by decide⟩])))) (.node (.node (.node (.leaf [⟨0, by decide⟩,⟨11, by decide⟩]) (.leaf [⟨7, by decide⟩,⟨11, by decide⟩])) (.node (.leaf [⟨1, by decide⟩,⟨2, by decide⟩,⟨11, by decide⟩]) (.leaf [⟨2, by decide⟩,⟨11, by decide⟩]))) (.node (.node (.leaf [⟨1, by decide⟩,⟨2, by decide⟩]) (.leaf [⟨9, by decide⟩,⟨11, by decide⟩])) (.node (.leaf [⟨5, by decide⟩,⟨11, by decide⟩]) (.leaf [])))))

def SuccessorSubset (q : Fin 16) : Finset (Fin 12) := (SuccessorSubsetTree.get q.val).toFinset

def SuccessorLetters : Array Nat := #[0,2,0,2,1,3,1,3]

def SuccessorLetter (c : Fin 8) : Fin 4 := Fin.ofNat 4 (SuccessorLetters[c.val]!)

theorem SuccessorProjectionCheck : ProjectionCheck SuccessorProduct SuccessorRaw SuccessorLetter SuccessorSubset := by decide +kernel

def SuccessorToRawPairs : Array (Fin 13 × Fin 16) := #[(⟨0, by decide⟩,⟨0, by decide⟩),(⟨0, by decide⟩,⟨1, by decide⟩),(⟨12, by decide⟩,⟨2, by decide⟩),(⟨1, by decide⟩,⟨3, by decide⟩),(⟨2, by decide⟩,⟨4, by decide⟩),(⟨1, by decide⟩,⟨5, by decide⟩),(⟨3, by decide⟩,⟨6, by decide⟩),(⟨4, by decide⟩,⟨7, by decide⟩),(⟨5, by decide⟩,⟨8, by decide⟩),(⟨6, by decide⟩,⟨9, by decide⟩),(⟨7, by decide⟩,⟨10, by decide⟩),(⟨8, by decide⟩,⟨11, by decide⟩),(⟨9, by decide⟩,⟨12, by decide⟩),(⟨10, by decide⟩,⟨13, by decide⟩),(⟨11, by decide⟩,⟨14, by decide⟩)]

def SuccessorToRawNodes : Lookup (Fin 13 × Fin 16) := (.node (.node (.node (.node (.leaf (⟨0, by decide⟩,⟨0, by decide⟩)) (.leaf (⟨5, by decide⟩,⟨8, by decide⟩))) (.node (.leaf (⟨2, by decide⟩,⟨4, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨12, by decide⟩)))) (.node (.node (.leaf (⟨12, by decide⟩,⟨2, by decide⟩)) (.leaf (⟨7, by decide⟩,⟨10, by decide⟩))) (.node (.leaf (⟨3, by decide⟩,⟨6, by decide⟩)) (.leaf (⟨11, by decide⟩,⟨14, by decide⟩))))) (.node (.node (.node (.leaf (⟨0, by decide⟩,⟨1, by decide⟩)) (.leaf (⟨6, by decide⟩,⟨9, by decide⟩))) (.node (.leaf (⟨1, by decide⟩,⟨5, by decide⟩)) (.leaf (⟨10, by decide⟩,⟨13, by decide⟩)))) (.node (.node (.leaf (⟨1, by decide⟩,⟨3, by decide⟩)) (.leaf (⟨8, by decide⟩,⟨11, by decide⟩))) (.node (.leaf (⟨4, by decide⟩,⟨7, by decide⟩)) (.leaf (⟨11, by decide⟩,⟨14, by decide⟩))))))

def SuccessorToRawNode (q : Fin 15) := SuccessorToRawNodes.get q.val

def SuccessorToRawEdges : Array (Array Nat) := #[#[1,2,3,4],#[1,2,5,4],#[2,2,2,2],#[2,6,2,2],#[7,2,2,2],#[2,6,2,2],#[8,2,2,2],#[9,2,2,2],#[10,2,2,2],#[11,2,2,2],#[12,2,2,2],#[1,2,13,2],#[14,13,2,2],#[2,2,2,2],#[2,6,2,2]]

def SuccessorToRawEdgeTree : Lookup Nat := (.node (.node (.node (.node (.node (.node (.leaf 1) (.leaf 10)) (.node (.leaf 7) (.leaf 14))) (.node (.node (.leaf 2) (.leaf 12)) (.node (.leaf 8) (.leaf 2)))) (.node (.node (.node (.leaf 1) (.leaf 11)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 1)) (.node (.leaf 9) (.leaf 2))))) (.node (.node (.node (.node (.leaf 3) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2)))) (.node (.node (.node (.leaf 5) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 13)) (.node (.leaf 2) (.leaf 2)))))) (.node (.node (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 13))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 6)))) (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 6) (.leaf 2))) (.node (.node (.leaf 6) (.leaf 2)) (.node (.leaf 2) (.leaf 6))))) (.node (.node (.node (.node (.leaf 4) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2)))) (.node (.node (.node (.leaf 4) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2)))))))

def SuccessorToRawEdge (q : Fin 15) (c : Fin 4) : Fin 15 := Fin.ofNat 15 (SuccessorToRawEdgeTree.get (q.val*4+c.val))

theorem SuccessorToRawValid : CoverValid Successor SuccessorRaw SuccessorToRawNode 0 SuccessorToRawEdge := by decide +kernel

theorem SuccessorToRaw (w) : accepts Successor w → accepts SuccessorRaw w :=
  cover_inclusion _ _ _ _ _ SuccessorToRawValid w

theorem SuccessorSound (w) (hw : accepts Successor w) :
    ∃ u, u.map SuccessorLetter = w ∧ accepts SuccessorProduct u :=
  projection_sound _ _ _ _ (projectionCheck_valid _ _ _ _ SuccessorProjectionCheck) w (SuccessorToRaw w hw)

#print axioms SuccessorSound

end CloitreCollaboration.Certificate.Operations
