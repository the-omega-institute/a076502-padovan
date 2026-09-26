import ConcreteCertificates

import Generated.GraphDomain

set_option maxRecDepth 1000000

set_option maxHeartbeats 0

namespace CloitreCollaboration.Certificate.Operations

def totalGraphPairs : Array (Fin 10 × Fin 7) := #[(⟨0, by decide⟩,⟨0, by decide⟩),(⟨1, by decide⟩,⟨0, by decide⟩),(⟨9, by decide⟩,⟨1, by decide⟩),(⟨2, by decide⟩,⟨0, by decide⟩),(⟨9, by decide⟩,⟨2, by decide⟩),(⟨9, by decide⟩,⟨6, by decide⟩),(⟨3, by decide⟩,⟨0, by decide⟩),(⟨9, by decide⟩,⟨3, by decide⟩),(⟨4, by decide⟩,⟨1, by decide⟩),(⟨9, by decide⟩,⟨4, by decide⟩),(⟨5, by decide⟩,⟨2, by decide⟩),(⟨9, by decide⟩,⟨0, by decide⟩),(⟨9, by decide⟩,⟨5, by decide⟩),(⟨6, by decide⟩,⟨3, by decide⟩),(⟨7, by decide⟩,⟨4, by decide⟩),(⟨8, by decide⟩,⟨5, by decide⟩)]

def totalGraphNodes : Lookup (Fin 10 × Fin 7) := (.node (.node (.node (.node (.leaf (⟨0, by decide⟩,⟨0, by decide⟩)) (.leaf (⟨4, by decide⟩,⟨1, by decide⟩))) (.node (.leaf (⟨9, by decide⟩,⟨2, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨5, by decide⟩)))) (.node (.node (.leaf (⟨9, by decide⟩,⟨1, by decide⟩)) (.leaf (⟨5, by decide⟩,⟨2, by decide⟩))) (.node (.leaf (⟨3, by decide⟩,⟨0, by decide⟩)) (.leaf (⟨7, by decide⟩,⟨4, by decide⟩))))) (.node (.node (.node (.leaf (⟨1, by decide⟩,⟨0, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨4, by decide⟩))) (.node (.leaf (⟨9, by decide⟩,⟨6, by decide⟩)) (.leaf (⟨6, by decide⟩,⟨3, by decide⟩)))) (.node (.node (.leaf (⟨2, by decide⟩,⟨0, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨0, by decide⟩))) (.node (.leaf (⟨9, by decide⟩,⟨3, by decide⟩)) (.leaf (⟨8, by decide⟩,⟨5, by decide⟩))))))

def totalGraphNode (q : Fin 16) := totalGraphNodes.get q.val

def totalGraphEdges : Array (Array Nat) := #[#[1,2],#[3,2],#[4,5],#[6,2],#[7,5],#[5,5],#[6,8],#[9,5],#[10,5],#[11,12],#[13,5],#[11,2],#[5,5],#[14,5],#[6,15],#[5,5]]

def totalGraphEdgeTree : Lookup Nat := (.node (.node (.node (.node (.node (.leaf 1) (.leaf 10)) (.node (.leaf 7) (.leaf 5))) (.node (.node (.leaf 4) (.leaf 13)) (.node (.leaf 6) (.leaf 6)))) (.node (.node (.node (.leaf 3) (.leaf 11)) (.node (.leaf 5) (.leaf 14))) (.node (.node (.leaf 6) (.leaf 11)) (.node (.leaf 9) (.leaf 5))))) (.node (.node (.node (.node (.leaf 2) (.leaf 5)) (.node (.leaf 5) (.leaf 5))) (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 8) (.leaf 15)))) (.node (.node (.node (.leaf 2) (.leaf 12)) (.node (.leaf 5) (.leaf 5))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 5) (.leaf 5))))))

def totalGraphEdge (q : Fin 16) (c : Fin 2) : Fin 16 := Fin.ofNat 16 (totalGraphEdgeTree.get (q.val*2+c.val))

theorem totalGraphValid : CoverValid Concrete.graphTotalityLeft GraphDomain totalGraphNode 0 totalGraphEdge := by decide +kernel

theorem totalGraph (w) : accepts Concrete.graphTotalityLeft w → accepts GraphDomain w :=
  cover_inclusion _ _ _ _ _ totalGraphValid w

end CloitreCollaboration.Certificate.Operations
