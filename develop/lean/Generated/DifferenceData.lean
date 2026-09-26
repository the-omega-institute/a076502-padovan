import AutomataCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0

namespace CloitreCollaboration.Certificate.Operations

def dTransitionTree : Lookup Int := (.node (.node (.node (.node (.node (.node (.leaf (0)) (.leaf (19))) (.node (.leaf (11)) (.leaf (26)))) (.node (.node (.leaf (5)) (.leaf (24))) (.node (.leaf (15)) (.leaf (26))))) (.node (.node (.node (.leaf (3)) (.leaf (22))) (.node (.leaf (13)) (.leaf (23)))) (.node (.node (.leaf (-1)) (.leaf (9))) (.node (.leaf (17)) (.leaf (23)))))) (.node (.node (.node (.node (.leaf (2)) (.leaf (20))) (.node (.leaf (5)) (.leaf (20)))) (.node (.node (.leaf (7)) (.leaf (-1))) (.node (.leaf (16)) (.leaf (20))))) (.node (.node (.node (.leaf (4)) (.leaf (23))) (.node (.leaf (14)) (.leaf (15)))) (.node (.node (.leaf (9)) (.leaf (25))) (.node (.leaf (18)) (.leaf (15))))))) (.node (.node (.node (.node (.node (.leaf (1)) (.leaf (-1))) (.node (.leaf (-1)) (.leaf (1)))) (.node (.node (.leaf (6)) (.leaf (1))) (.node (.leaf (-1)) (.leaf (1))))) (.node (.node (.node (.leaf (-1)) (.leaf (-1))) (.node (.leaf (-1)) (.leaf (8)))) (.node (.node (.leaf (-1)) (.leaf (21))) (.node (.leaf (-1)) (.leaf (8)))))) (.node (.node (.node (.node (.leaf (-1)) (.leaf (21))) (.node (.leaf (12)) (.leaf (27)))) (.node (.node (.leaf (8)) (.leaf (-1))) (.node (.leaf (-1)) (.leaf (27))))) (.node (.node (.node (.leaf (-1)) (.leaf (21))) (.node (.leaf (-1)) (.leaf (-1)))) (.node (.node (.leaf (10)) (.leaf (10))) (.node (.leaf (-1)) (.leaf (-1))))))))

def dOutputTree : Lookup Int := (.node (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 0) (.leaf 1)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))) (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 1))))))

def dTransitions (q : Fin 28) (b : Bool) : Int := dTransitionTree.get (2*q.val + if b then 1 else 0)

def dOutput (q : Fin 28) : Int := dOutputTree.get q.val

theorem d_binary : ∀ q : Fin 28, dOutput q = 0 ∨ dOutput q = 1 := by decide +kernel

end CloitreCollaboration.Certificate.Operations
