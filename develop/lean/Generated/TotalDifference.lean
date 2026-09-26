import ConcreteCertificates

import Generated.Difference

set_option maxRecDepth 1000000

set_option maxHeartbeats 0

namespace CloitreCollaboration.Certificate.Operations

def totalDifferencePairs : Array (Fin 10 × Fin 13) := #[(⟨0, by decide⟩,⟨0, by decide⟩),(⟨1, by decide⟩,⟨1, by decide⟩),(⟨9, by decide⟩,⟨2, by decide⟩),(⟨2, by decide⟩,⟨1, by decide⟩),(⟨9, by decide⟩,⟨3, by decide⟩),(⟨9, by decide⟩,⟨4, by decide⟩),(⟨9, by decide⟩,⟨12, by decide⟩),(⟨3, by decide⟩,⟨1, by decide⟩),(⟨9, by decide⟩,⟨5, by decide⟩),(⟨9, by decide⟩,⟨6, by decide⟩),(⟨4, by decide⟩,⟨3, by decide⟩),(⟨9, by decide⟩,⟨7, by decide⟩),(⟨9, by decide⟩,⟨8, by decide⟩),(⟨5, by decide⟩,⟨5, by decide⟩),(⟨9, by decide⟩,⟨9, by decide⟩),(⟨9, by decide⟩,⟨10, by decide⟩),(⟨6, by decide⟩,⟨7, by decide⟩),(⟨9, by decide⟩,⟨1, by decide⟩),(⟨9, by decide⟩,⟨11, by decide⟩),(⟨7, by decide⟩,⟨9, by decide⟩),(⟨8, by decide⟩,⟨11, by decide⟩)]

def totalDifferenceNodes : Lookup (Fin 10 × Fin 13) := (.node (.node (.node (.node (.node (.leaf (⟨0, by decide⟩,⟨0, by decide⟩)) (.leaf (⟨6, by decide⟩,⟨7, by decide⟩))) (.node (.leaf (⟨9, by decide⟩,⟨5, by decide⟩)) (.leaf (⟨6, by decide⟩,⟨7, by decide⟩)))) (.node (.node (.leaf (⟨9, by decide⟩,⟨3, by decide⟩)) (.leaf (⟨8, by decide⟩,⟨11, by decide⟩))) (.node (.leaf (⟨9, by decide⟩,⟨8, by decide⟩)) (.leaf (⟨8, by decide⟩,⟨11, by decide⟩))))) (.node (.node (.node (.leaf (⟨9, by decide⟩,⟨2, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨11, by decide⟩))) (.node (.leaf (⟨4, by decide⟩,⟨3, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨11, by decide⟩)))) (.node (.node (.leaf (⟨9, by decide⟩,⟨12, by decide⟩)) (.leaf (⟨8, by decide⟩,⟨11, by decide⟩))) (.node (.leaf (⟨9, by decide⟩,⟨9, by decide⟩)) (.leaf (⟨8, by decide⟩,⟨11, by decide⟩)))))) (.node (.node (.node (.node (.leaf (⟨1, by decide⟩,⟨1, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨1, by decide⟩))) (.node (.leaf (⟨9, by decide⟩,⟨6, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨1, by decide⟩)))) (.node (.node (.leaf (⟨9, by decide⟩,⟨4, by decide⟩)) (.leaf (⟨8, by decide⟩,⟨11, by decide⟩))) (.node (.leaf (⟨5, by decide⟩,⟨5, by decide⟩)) (.leaf (⟨8, by decide⟩,⟨11, by decide⟩))))) (.node (.node (.node (.leaf (⟨2, by decide⟩,⟨1, by decide⟩)) (.leaf (⟨7, by decide⟩,⟨9, by decide⟩))) (.node (.leaf (⟨9, by decide⟩,⟨7, by decide⟩)) (.leaf (⟨7, by decide⟩,⟨9, by decide⟩)))) (.node (.node (.leaf (⟨3, by decide⟩,⟨1, by decide⟩)) (.leaf (⟨8, by decide⟩,⟨11, by decide⟩))) (.node (.leaf (⟨9, by decide⟩,⟨10, by decide⟩)) (.leaf (⟨8, by decide⟩,⟨11, by decide⟩)))))))

def totalDifferenceNode (q : Fin 21) := totalDifferenceNodes.get q.val

def totalDifferenceEdges : Array (Array Nat) := #[#[1,2],#[3,4],#[5,6],#[7,4],#[8,6],#[9,6],#[6,6],#[7,10],#[11,6],#[12,6],#[13,6],#[14,6],#[15,6],#[16,6],#[17,18],#[17,2],#[19,6],#[17,4],#[6,6],#[7,20],#[6,6]]

def totalDifferenceEdgeTree : Lookup Nat := (.node (.node (.node (.node (.node (.node (.leaf 1) (.leaf 19)) (.node (.leaf 11) (.leaf 19))) (.node (.node (.leaf 8) (.leaf 6)) (.node (.leaf 15) (.leaf 6)))) (.node (.node (.node (.leaf 5) (.leaf 6)) (.node (.leaf 13) (.leaf 6))) (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 17) (.leaf 6))))) (.node (.node (.node (.node (.leaf 3) (.leaf 17)) (.node (.leaf 12) (.leaf 17))) (.node (.node (.leaf 9) (.leaf 6)) (.node (.leaf 16) (.leaf 6)))) (.node (.node (.node (.leaf 7) (.leaf 7)) (.node (.leaf 14) (.leaf 7))) (.node (.node (.leaf 7) (.leaf 6)) (.node (.leaf 17) (.leaf 6)))))) (.node (.node (.node (.node (.node (.leaf 2) (.leaf 6)) (.node (.leaf 6) (.leaf 6))) (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 6) (.leaf 6)))) (.node (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 6) (.leaf 6))) (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 18) (.leaf 6))))) (.node (.node (.node (.node (.leaf 4) (.leaf 4)) (.node (.leaf 6) (.leaf 4))) (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 6) (.leaf 6)))) (.node (.node (.node (.leaf 4) (.leaf 20)) (.node (.leaf 6) (.leaf 20))) (.node (.node (.leaf 10) (.leaf 6)) (.node (.leaf 2) (.leaf 6)))))))

def totalDifferenceEdge (q : Fin 21) (c : Fin 2) : Fin 21 := Fin.ofNat 21 (totalDifferenceEdgeTree.get (q.val*2+c.val))

theorem totalDifferenceValid : CoverValid Concrete.differenceLanguageLeft Difference totalDifferenceNode 0 totalDifferenceEdge := by decide +kernel

theorem totalDifference (w) : accepts Concrete.differenceLanguageLeft w → accepts Difference w :=
  cover_inclusion _ _ _ _ _ totalDifferenceValid w

end CloitreCollaboration.Certificate.Operations
