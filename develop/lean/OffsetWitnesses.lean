import CanonicalCandidate

set_option autoImplicit false

namespace CloitreCollaboration.Candidate

theorem b_one : b 1=1 := by
  rw [b_on_word 1 [true] (by unfold Greedy.AcceptsFrom; decide) (by decide)]
  decide

theorem b_two : b 2=1 := by
  rw [b_on_word 2 [true,false] (by unfold Greedy.AcceptsFrom; decide) (by decide)]
  decide

theorem b_ninety_three : b 93=54 := by
  rw [b_on_word 93 [true,false,false,false,false,false,false,false,false,true,
    false,false,false,false,false] (by unfold Greedy.AcceptsFrom; decide) (by decide)]
  decide

theorem b_1167 : b 1167=664 := by
  rw [b_on_word 1167 [true,false,false,false,false,false,false,false,false,true,
    false,false,false,false,false,false,false,false,false,false,false,false,false,false]
    (by unfold Greedy.AcceptsFrom; decide) (by decide)]
  decide

theorem slope_bracket :
    569840290998/1000000000000 < Discrepancy.slope ∧
      Discrepancy.slope < 569840290999/1000000000000 := by
  have hb := Discrepancy.inverse_square_bounds Discrepancy.rho
    Discrepancy.rho_gt_one Discrepancy.rho_cubic
  apply Discrepancy.coefficient_bracket
  · unfold Discrepancy.slope; linarith [hb.1]
  · unfold Discrepancy.slope; linarith [hb.2]
  · exact Discrepancy.slope_cubic

theorem witness_floors :
    ⌊Discrepancy.slope*(1 : ℝ)⌋=(0 : Int) ∧
    ⌊Discrepancy.slope*(2 : ℝ)⌋=(1 : Int) ∧
    ⌊Discrepancy.slope*(93 : ℝ)⌋=(52 : Int) ∧
    ⌊Discrepancy.slope*(1167 : ℝ)⌋=(665 : Int) := by
  obtain ⟨hl,hu⟩ := slope_bracket
  repeat' constructor
  all_goals rw [Int.floor_eq_iff]
  all_goals norm_num
  all_goals constructor <;> linarith

theorem offset_witnesses :
    b 1-⌊Discrepancy.slope*(1 : ℝ)⌋=1 ∧
    b 2-⌊Discrepancy.slope*(2 : ℝ)⌋=0 ∧
    b 93-⌊Discrepancy.slope*(93 : ℝ)⌋=2 ∧
    b 1167-⌊Discrepancy.slope*(1167 : ℝ)⌋= -1 := by
  obtain ⟨h1,h2,h93,h1167⟩ := witness_floors
  rw [b_one,b_two,b_ninety_three,b_1167,h1,h2,h93,h1167]
  decide

#print axioms offset_witnesses

end CloitreCollaboration.Candidate
