import MorphicEnumeration
import FirstDifference

set_option autoImplicit false

namespace CloitreCollaboration.Morphic

open Certificate.Difference

/-- The literal A076502 first-difference sequence has the concrete 26-letter
non-erasing substitution and non-erasing output presentation defined in Morphic. -/
theorem sequence_morphic (a : Nat -> Nat) (hzero : a 0 = 0) (hone : a 1 = 1)
    (ha : NestedRecurrence a) (n : Nat) :
    (a (n+1) : Int) - (a n : Int) = Greedy.bitValue (morphicWord n) := by
  rw [sequence_first_difference a hzero hone ha n]
  exact (morphicWord_at_rep (Candidate.representation n) (Candidate.representation_legal n)
    n (Candidate.representation_value n)).symm

/-- Every finite non-erasing substitution approximant supplies exact sequence differences. -/
theorem sequence_morphic_prefix (a : Nat -> Nat) (hzero : a 0 = 0) (hone : a 1 = 1)
    (ha : NestedRecurrence a) (k i : Nat) (hi : i < (outputPrefix k).length) :
    (a (i+1) : Int) - (a i : Int) = Greedy.bitValue ((outputPrefix k)[i]!) := by
  rw [sequence_morphic a hzero hone ha i, morphicWord_prefix k i hi]

theorem sequence_binary (a : Nat -> Nat) (hzero : a 0 = 0) (hone : a 1 = 1)
    (ha : NestedRecurrence a) (n : Nat) : a (n+1) = a n \/ a (n+1) = a n + 1 := by
  have h := sequence_morphic a hzero hone ha n
  cases hw : morphicWord n <;> simp [hw, Greedy.bitValue] at h <;> omega

theorem sequence_monotone (a : Nat -> Nat) (hzero : a 0 = 0) (hone : a 1 = 1)
    (ha : NestedRecurrence a) : Monotone a := by
  apply monotone_nat_of_le_succ
  intro n
  rcases sequence_binary a hzero hone ha n with h | h <;> omega

#print axioms sequence_morphic
#print axioms sequence_morphic_prefix
#print axioms sequence_binary

end CloitreCollaboration.Morphic
