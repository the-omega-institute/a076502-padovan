import CandidateDiscrepancy
import RepresentationIndependence
import PrimitiveSemantics

set_option autoImplicit false

namespace CloitreCollaboration.Candidate

noncomputable section

open Certificate.Primitive

def representation (n : Nat) : List Bool := Classical.choose (Greedy.every_nat_dfa n)

theorem representation_legal (n : Nat) : Greedy.AcceptsFrom 4 (representation n) :=
  (Classical.choose_spec (Greedy.every_nat_dfa n)).1

theorem representation_value (n : Nat) :
    WordArithmetic.wordValue Greedy.bitValue (representation n)=(n : Int) :=
  (Classical.choose_spec (Greedy.every_nat_dfa n)).2

def eOutput (bs : List Bool) : Int := Suffix.output (eRun 0 bs)

theorem eOutput_leading_zero (bs : List Bool) : eOutput (false::bs)=eOutput bs := by
  have hs : eStep 0 false=0 := by decide
  simp only [eOutput,eRun,List.foldl_cons,hs]

def b (n : Nat) : Int := WordArithmetic.shiftValue Greedy.bitValue (representation n)+
  eOutput (representation n)

theorem b_on_word (n : Nat) (bs : List Bool) (hlegal : Greedy.AcceptsFrom 4 bs)
    (hvalue : WordArithmetic.wordValue Greedy.bitValue bs=(n : Int)) :
    b n=WordArithmetic.shiftValue Greedy.bitValue bs+eOutput bs := by
  unfold b
  apply Greedy.candidate_representation_independent eOutput eOutput_leading_zero
  · exact representation_legal n
  · exact hlegal
  · rw [representation_value,hvalue]

theorem b_on_path (n : Nat) (bs : List Bool) (last : Fin 28)
    (hlegal : Greedy.AcceptsFrom 4 bs)
    (hvalue : WordArithmetic.wordValue Greedy.bitValue bs=(n : Int))
    (hp : Suffix.Path 0 bs last) : b n=wordCandidate bs last := by
  rw [b_on_word n bs hlegal hvalue]
  unfold wordCandidate shiftedValue selected shiftWeight eOutput
  rw [Greedy.positions_shift_value,eRun_of_path hp]

theorem b_discrepancy (n : Nat) (bs : List Bool) (last : Fin 28)
    (hlegal : Greedy.AcceptsFrom 4 bs)
    (hvalue : WordArithmetic.wordValue Greedy.bitValue bs=(n : Int))
    (hp : Suffix.Path 0 bs last) :
    -2 < (b n : ℝ)-Discrepancy.slope*n ∧ (b n : ℝ)-Discrepancy.slope*n < 2 := by
  have hb := word_error Discrepancy.rho Discrepancy.rho_gt_one Discrepancy.rho_cubic
    bs last ((Greedy.dfa_accepts_iff bs).mp hlegal) hp
  have hv : wordValue bs=(n : Int) := (Greedy.positions_word_value bs).trans hvalue
  rw [← b_on_path n bs last hlegal hvalue hp,hv] at hb
  simpa [Discrepancy.slope] using hb

theorem b_sharp_discrepancy (n : Nat) (bs : List Bool) (last : Fin 28)
    (hlegal : Greedy.AcceptsFrom 4 bs)
    (hvalue : WordArithmetic.wordValue Greedy.bitValue bs=(n : Int))
    (hp : Suffix.Path 0 bs last) :
    -11/10 < (b n : ℝ)-Discrepancy.slope*n ∧ (b n : ℝ)-Discrepancy.slope*n < 6/5 := by
  have hb := word_sharp_error Discrepancy.rho Discrepancy.rho_gt_one Discrepancy.rho_cubic
    bs last ((Greedy.dfa_accepts_iff bs).mp hlegal) hp
  have hv : wordValue bs=(n : Int) := (Greedy.positions_word_value bs).trans hvalue
  rw [← b_on_path n bs last hlegal hvalue hp,hv] at hb
  simpa [Discrepancy.slope] using hb

/-- Only existence of legal output paths is needed; their numeric values are already fixed. -/
theorem b_limit
    (htotal : ∀ n : Nat, ∃ bs last, Greedy.AcceptsFrom 4 bs ∧
      WordArithmetic.wordValue Greedy.bitValue bs=(n : Int) ∧ Suffix.Path 0 bs last) :
    Filter.Tendsto (fun n : Nat => (b n : ℝ)/n) Filter.atTop (nhds Discrepancy.slope) := by
  apply Discrepancy.bounded_discrepancy_limit (fun n => (b n : ℝ)) Discrepancy.slope 2
  intro n
  obtain ⟨bs,last,hl,hv,hp⟩ := htotal n
  obtain ⟨hlo,hhi⟩ := b_discrepancy n bs last hl hv hp
  exact (abs_lt.mpr ⟨hlo,hhi⟩).le

theorem b_offsets (n : Nat) (bs : List Bool) (last : Fin 28)
    (hlegal : Greedy.AcceptsFrom 4 bs)
    (hvalue : WordArithmetic.wordValue Greedy.bitValue bs=(n : Int))
    (hp : Suffix.Path 0 bs last) :
    b n-⌊Discrepancy.slope*n⌋ ∈ ({-1,0,1,2} : Finset Int) := by
  obtain ⟨hl,hu⟩ := b_discrepancy n bs last hlegal hvalue hp
  exact Discrepancy.floor_offsets _ _ hl hu

#print axioms b_on_path
#print axioms b_discrepancy
#print axioms b_limit

end

end CloitreCollaboration.Candidate
