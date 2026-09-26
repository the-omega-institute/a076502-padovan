import FinalIdentification

set_option autoImplicit false

namespace CloitreCollaboration.ComputableSequence

open Certificate.Identification

/-- The clamps make well-foundedness syntactic. They are inactive on the proved sequence. -/
def eval : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 =>
      let i := min (n+2-eval (n+1)) (n+1)
      let j := min (n+2-eval i) (n+1)
      n+2-eval j
termination_by n => n
decreasing_by all_goals omega

theorem eval_eq_bNat (N : Nat) : eval N = bNat N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    rcases N with _ | _ | n
    · simpa only [eval] using bNat_zero.symm
    · change eval 1 = bNat 1
      simpa only [eval] using bNat_one.symm
    · have hp := ih (n+1) (by omega)
      have h1 := bNat_bounds (n+1) (by omega)
      have hi : n+2-bNat (n+1) ≤ n+1 := by omega
      have hipos : 1 ≤ n+2-bNat (n+1) := by omega
      have hip := ih (n+2-bNat (n+1)) (by omega)
      have h2 := bNat_bounds (n+2-bNat (n+1)) hipos
      have hj : n+2-bNat (n+2-bNat (n+1)) ≤ n+1 := by omega
      have hjp := ih (n+2-bNat (n+2-bNat (n+1))) (by omega)
      rw [eval,hp,min_eq_left hi,hip,min_eq_left hj,hjp]
      have hr := bNat_recurrence (n+2) (by omega)
      have he : n+2-1 = n+1 := by omega
      rw [he] at hr
      exact hr.symm

theorem eval_cast (n : Nat) : (eval n : Int) = Candidate.b n := by
  rw [eval_eq_bNat,bNat_cast]

#print axioms eval_eq_bNat

end CloitreCollaboration.ComputableSequence
