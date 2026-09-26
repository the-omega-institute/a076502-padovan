import MorphicIdentification
import SequenceConsequences
import ComputableSequence

set_option autoImplicit false

namespace CloitreCollaboration.Morphic

open Certificate.Identification
open scoped BigOperators

/-- Number of letters 1 in the length-len factor beginning at i. -/
def ones (i len : Nat) : Nat :=
  ∑ k ∈ Finset.range len, if morphicWord (i+k) then 1 else 0

theorem ones_card (i len : Nat) : ones i len =
    ((Finset.range len).filter (fun k => morphicWord (i+k) = true)).card := by
  simp only [ones, Finset.card_filter]

/-- Exact telescoping identity for every finite factor of the infinite binary word. -/
theorem factor_ones (i len : Nat) :
    (ones i len : Int) = (bNat (i+len) : Int) - bNat i := by
  induction len with
  | zero => simp [ones]
  | succ len ih =>
      have hd := sequence_morphic bNat bNat_zero bNat_one bNat_recurrence (i+len)
      have hs : ones i (len+1) = ones i len + (if morphicWord (i+len) then 1 else 0) :=
        Finset.sum_range_succ _ _
      rw [hs, Nat.cast_add, ih]
      have he : i + (len+1) = (i+len)+1 := by omega
      rw [he]
      cases hw : morphicWord (i+len) <;> simp [hw, Greedy.bitValue] at hd ⊢ <;> omega

theorem factor_ones_nat (i len : Nat) : ones i len = bNat (i+len) - bNat i := by
  have h := factor_ones i len
  omega

/-- The first N letters contain exactly a(N) ones, including d(0)=1. -/
theorem prefix_ones (N : Nat) : ones 0 N = bNat N := by
  simpa [bNat_zero] using factor_ones_nat 0 N

theorem prefix_ones_computable (N : Nat) : ones 0 N = ComputableSequence.eval N := by
  rw [prefix_ones, ComputableSequence.eval_eq_bNat]

/-- The frequency of the letter 1 exists and is the cubic slope. -/
theorem ones_frequency :
    Filter.Tendsto (fun N : Nat => (ones 0 N : Real) / N)
      Filter.atTop (nhds Discrepancy.slope) := by
  simpa only [prefix_ones] using sequence_limit bNat bNat_zero bNat_one bNat_recurrence

/-- Any two equal-length factors differ by at most four occurrences of the letter 1. -/
theorem word_four_balanced (i j len : Nat) :
    |(ones i len : Int) - (ones j len : Int)| <= 4 := by
  rw [factor_ones, factor_ones]
  exact sequence_four_balanced bNat bNat_zero bNat_one bNat_recurrence i j len

theorem word_not_eventually_periodic :
    ¬ exists N p : Nat, 0 < p /\ forall n, N <= n -> morphicWord (n+p) = morphicWord n := by
  rintro ⟨N,p,hp,hper⟩
  apply sequence_not_eventually_periodic bNat bNat_zero bNat_one bNat_recurrence
  refine ⟨N,p,hp,?_⟩
  intro n hn
  rw [sequence_morphic bNat bNat_zero bNat_one bNat_recurrence (n+p),
    sequence_morphic bNat bNat_zero bNat_one bNat_recurrence n, hper n hn]

#print axioms prefix_ones
#print axioms ones_frequency
#print axioms word_four_balanced
#print axioms word_not_eventually_periodic

end CloitreCollaboration.Morphic
