import WordConsequences

set_option autoImplicit false

namespace CloitreCollaboration.Candidate

theorem b_135 : b 135 = 76 := by
  rw [b_on_word 135 [true,false,false,false,false,false,true,false,false,false,
    false,false,false,false,false,false]
    (by unfold Greedy.AcceptsFrom; decide) (by decide)]
  decide

theorem b_207 : b 207 = 119 := by
  rw [b_on_word 207 [true,false,false,false,false,false,false,false,false,false,
    false,false,true,false,false,false,false,false]
    (by unfold Greedy.AcceptsFrom; decide) (by decide)]
  decide

theorem b_214 : b 214 = 123 := by
  rw [b_on_word 214 [true,false,false,false,false,false,false,false,false,false,
    true,false,false,false,false,false,true,false]
    (by unfold Greedy.AcceptsFrom; decide) (by decide)]
  decide

theorem b_286 : b 286 = 162 := by
  rw [b_on_word 286 [true,false,false,false,false,false,false,false,false,true,
    false,false,false,false,false,false,false,false,false]
    (by unfold Greedy.AcceptsFrom; decide) (by decide)]
  decide

end CloitreCollaboration.Candidate

namespace CloitreCollaboration.Morphic

open Certificate.Identification

/-- Cloitre's two length-72 factors attain the balance bound. -/
theorem balance_witnesses : ones 135 72 = 43 ∧ ones 214 72 = 39 := by
  have hleft := factor_ones 135 72
  have hright := factor_ones 214 72
  norm_num only [Nat.reduceAdd, bNat_cast, Candidate.b_135, Candidate.b_207,
    Candidate.b_214, Candidate.b_286] at hleft hright
  omega

def IsBalanced (C : Nat) : Prop :=
  ∀ i j len : Nat, |(ones i len : Int)-(ones j len : Int)| ≤ (C : Int)

/-- The minimum uniform balance constant is exactly four. -/
theorem exact_balance (C : Nat) : IsBalanced C ↔ 4 ≤ C := by
  constructor
  · intro h
    have hw := h 135 214 72
    rw [balance_witnesses.1, balance_witnesses.2] at hw
    norm_num at hw
    omega
  · intro h i j len
    exact (word_four_balanced i j len).trans (by exact_mod_cast h)

theorem not_three_balanced : ¬ IsBalanced 3 := by
  rw [exact_balance]
  omega

#print axioms balance_witnesses
#print axioms exact_balance

end CloitreCollaboration.Morphic
