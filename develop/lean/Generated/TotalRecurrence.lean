import ConcreteCertificates

import Generated.Recurrence

set_option maxRecDepth 1000000

set_option maxHeartbeats 0

namespace CloitreCollaboration.Certificate.Operations

def totalRecurrencePairs : Array (Fin 12 × Fin 8) := #[(⟨0, by decide⟩,⟨0, by decide⟩),(⟨1, by decide⟩,⟨0, by decide⟩),(⟨11, by decide⟩,⟨1, by decide⟩),(⟨2, by decide⟩,⟨0, by decide⟩),(⟨11, by decide⟩,⟨2, by decide⟩),(⟨11, by decide⟩,⟨7, by decide⟩),(⟨3, by decide⟩,⟨0, by decide⟩),(⟨11, by decide⟩,⟨3, by decide⟩),(⟨4, by decide⟩,⟨1, by decide⟩),(⟨11, by decide⟩,⟨4, by decide⟩),(⟨5, by decide⟩,⟨2, by decide⟩),(⟨11, by decide⟩,⟨5, by decide⟩),(⟨11, by decide⟩,⟨6, by decide⟩),(⟨6, by decide⟩,⟨3, by decide⟩),(⟨7, by decide⟩,⟨4, by decide⟩),(⟨8, by decide⟩,⟨5, by decide⟩),(⟨9, by decide⟩,⟨6, by decide⟩),(⟨10, by decide⟩,⟨1, by decide⟩)]

def totalRecurrenceNodes : Lookup (Fin 12 × Fin 8) := (.node (.node (.node (.node (.node (.leaf (⟨0, by decide⟩,⟨0, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨6, by decide⟩))) (.node (.leaf (⟨4, by decide⟩,⟨1, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨6, by decide⟩)))) (.node (.node (.leaf (⟨11, by decide⟩,⟨2, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨6, by decide⟩))) (.node (.leaf (⟨11, by decide⟩,⟨6, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨6, by decide⟩))))) (.node (.node (.node (.leaf (⟨11, by decide⟩,⟨1, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨6, by decide⟩))) (.node (.leaf (⟨5, by decide⟩,⟨2, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨6, by decide⟩)))) (.node (.node (.leaf (⟨3, by decide⟩,⟨0, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨6, by decide⟩))) (.node (.leaf (⟨7, by decide⟩,⟨4, by decide⟩)) (.leaf (⟨9, by decide⟩,⟨6, by decide⟩)))))) (.node (.node (.node (.node (.leaf (⟨1, by decide⟩,⟨0, by decide⟩)) (.leaf (⟨10, by decide⟩,⟨1, by decide⟩))) (.node (.leaf (⟨11, by decide⟩,⟨4, by decide⟩)) (.leaf (⟨10, by decide⟩,⟨1, by decide⟩)))) (.node (.node (.leaf (⟨11, by decide⟩,⟨7, by decide⟩)) (.leaf (⟨10, by decide⟩,⟨1, by decide⟩))) (.node (.leaf (⟨6, by decide⟩,⟨3, by decide⟩)) (.leaf (⟨10, by decide⟩,⟨1, by decide⟩))))) (.node (.node (.node (.leaf (⟨2, by decide⟩,⟨0, by decide⟩)) (.leaf (⟨10, by decide⟩,⟨1, by decide⟩))) (.node (.leaf (⟨11, by decide⟩,⟨5, by decide⟩)) (.leaf (⟨10, by decide⟩,⟨1, by decide⟩)))) (.node (.node (.leaf (⟨11, by decide⟩,⟨3, by decide⟩)) (.leaf (⟨10, by decide⟩,⟨1, by decide⟩))) (.node (.leaf (⟨8, by decide⟩,⟨5, by decide⟩)) (.leaf (⟨10, by decide⟩,⟨1, by decide⟩)))))))

def totalRecurrenceNode (q : Fin 18) := totalRecurrenceNodes.get q.val

def totalRecurrenceEdges : Array (Array Nat) := #[#[1,2],#[3,2],#[4,5],#[6,2],#[7,5],#[5,5],#[6,8],#[9,5],#[10,5],#[11,12],#[13,5],#[11,2],#[5,5],#[14,5],#[15,16],#[15,17],#[5,5],#[10,5]]

def totalRecurrenceEdgeTree : Lookup Nat := (.node (.node (.node (.node (.node (.node (.leaf 1) (.leaf 5)) (.node (.leaf 10) (.leaf 5))) (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 5) (.leaf 5)))) (.node (.node (.node (.leaf 4) (.leaf 5)) (.node (.leaf 13) (.leaf 5))) (.node (.node (.leaf 6) (.leaf 5)) (.node (.leaf 15) (.leaf 5))))) (.node (.node (.node (.node (.leaf 3) (.leaf 10)) (.node (.leaf 11) (.leaf 10))) (.node (.node (.leaf 5) (.leaf 10)) (.node (.leaf 14) (.leaf 10)))) (.node (.node (.node (.leaf 6) (.leaf 10)) (.node (.leaf 11) (.leaf 10))) (.node (.node (.leaf 9) (.leaf 10)) (.node (.leaf 15) (.leaf 10)))))) (.node (.node (.node (.node (.node (.leaf 2) (.leaf 5)) (.node (.leaf 5) (.leaf 5))) (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 5) (.leaf 5)))) (.node (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 5) (.leaf 5))) (.node (.node (.leaf 8) (.leaf 5)) (.node (.leaf 16) (.leaf 5))))) (.node (.node (.node (.node (.leaf 2) (.leaf 5)) (.node (.leaf 12) (.leaf 5))) (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 5) (.leaf 5)))) (.node (.node (.node (.leaf 2) (.leaf 5)) (.node (.leaf 2) (.leaf 5))) (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 17) (.leaf 5)))))))

def totalRecurrenceEdge (q : Fin 18) (c : Fin 2) : Fin 18 := Fin.ofNat 18 (totalRecurrenceEdgeTree.get (q.val*2+c.val))

theorem totalRecurrenceValid : CoverValid Concrete.recurrenceLanguageLeft Recurrence totalRecurrenceNode 0 totalRecurrenceEdge := by decide +kernel

theorem totalRecurrence (w) : accepts Concrete.recurrenceLanguageLeft w → accepts Recurrence w :=
  cover_inclusion _ _ _ _ _ totalRecurrenceValid w

end CloitreCollaboration.Certificate.Operations
