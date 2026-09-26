import SequenceConsequences
import MorphicIdentification
import EffectiveExtrema
import TightGlobalBound
import WordConsequences
import BalanceSharpness

set_option autoImplicit false

namespace CloitreCollaboration.Main

open Certificate.Identification

abbrev a := ComputableSequence.eval

theorem a_eq : a = bNat := funext ComputableSequence.eval_eq_bNat
theorem a_zero : a 0 = 0 := by rw [a_eq]; exact bNat_zero
theorem a_one : a 1 = 1 := by rw [a_eq]; exact bNat_one
theorem a_recurrence : NestedRecurrence a := by rw [a_eq]; exact bNat_recurrence

theorem identification (n : Nat) : (a n : Int) = Candidate.b n :=
  ComputableSequence.eval_cast n

theorem discrepancy (n : Nat) :
    -11/10 < (a n : ℝ)-Discrepancy.slope*n ∧
      (a n : ℝ)-Discrepancy.slope*n < 6/5 :=
  sequence_sharp_discrepancy a a_zero a_one a_recurrence n

theorem paper_discrepancy (n : Nat) :
    -1049234/1000000 < (a n : ℝ)-Discrepancy.slope*n ∧
      (a n : ℝ)-Discrepancy.slope*n < 1155081/1000000 :=
  sequence_tight_discrepancy a a_zero a_one a_recurrence n

theorem exact_offsets :
    Set.range (fun n : Nat => (a n : Int)-⌊Discrepancy.slope*n⌋) =
      ({-1,0,1,2} : Set Int) :=
  sequence_exact_offsets a a_zero a_one a_recurrence

theorem morphic (n : Nat) :
    (a (n+1) : Int)-(a n : Int) = Greedy.bitValue (Morphic.morphicWord n) :=
  Morphic.sequence_morphic a a_zero a_one a_recurrence n

theorem asymptotic :
    Filter.Tendsto (fun n : Nat => (a n : ℝ)/n) Filter.atTop (nhds Discrepancy.slope) :=
  sequence_limit a a_zero a_one a_recurrence

theorem not_eventually_periodic :
    ¬ ∃ N p : Nat, 0 < p ∧ ∀ n, N ≤ n →
      (a (n+p+1) : Int)-a (n+p) = (a (n+1) : Int)-a n :=
  sequence_not_eventually_periodic a a_zero a_one a_recurrence

theorem four_balanced (i j len : Nat) :
    |((a (i+len) : Int)-a i)-((a (j+len) : Int)-a j)| ≤ 4 :=
  sequence_four_balanced a a_zero a_one a_recurrence i j len

end CloitreCollaboration.Main

#print axioms CloitreCollaboration.Main.a_recurrence
#print axioms CloitreCollaboration.Main.identification
#print axioms CloitreCollaboration.Main.discrepancy
#print axioms CloitreCollaboration.Main.paper_discrepancy
#print axioms CloitreCollaboration.Main.exact_offsets
#print axioms CloitreCollaboration.Main.morphic
#print axioms CloitreCollaboration.Main.asymptotic
#print axioms CloitreCollaboration.Main.not_eventually_periodic
#print axioms CloitreCollaboration.Main.four_balanced
#print axioms CloitreCollaboration.EffectiveExtrema.global_enclosures
#print axioms CloitreCollaboration.EffectiveExtrema.widths_tendsto_zero
#print axioms CloitreCollaboration.EffectiveExtrema.endpoints_converge
#print axioms CloitreCollaboration.Morphic.prefix_ones_computable
#print axioms CloitreCollaboration.Morphic.ones_frequency
#print axioms CloitreCollaboration.Morphic.word_four_balanced
#print axioms CloitreCollaboration.Morphic.word_not_eventually_periodic
#print axioms CloitreCollaboration.Morphic.balance_witnesses
#print axioms CloitreCollaboration.Morphic.exact_balance
