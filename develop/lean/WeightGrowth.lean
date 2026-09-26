import GreedyRepresentation
import Mathlib.Tactic

set_option autoImplicit false

namespace CloitreCollaboration.Greedy

theorem U_exponential_bound (n : Nat) : U n < (2 : Int) ^ (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | _ | n
      · decide
      · decide
      · decide
      · decide
      · have h1 := ih (n + 2) (by omega)
        have h2 := ih (n + 1) (by omega)
        have hp : 0 < (2 : Int) ^ n := by positivity
        rw [U_recurrence]
        simp only [Nat.add_assoc, Nat.reduceAdd, pow_succ] at *
        omega

#print axioms U_exponential_bound

end CloitreCollaboration.Greedy
