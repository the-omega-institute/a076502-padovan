import GraphCandidate
import OffsetWitnesses

set_option autoImplicit false

namespace CloitreCollaboration.Candidate

noncomputable section

def error (n : Nat) : ℝ := (b n : ℝ)-Discrepancy.slope*n

theorem error_bounds (n : Nat) : -11/10 < error n ∧ error n < 6/5 := by
  obtain ⟨bs,last,hl,hv,hp⟩ := Certificate.Identification.all_paths n
  exact b_sharp_discrepancy n bs last hl hv hp

theorem four_balanced (i j len : Nat) :
    |(b (i+len)-b i)-(b (j+len)-b j)| ≤ (4 : Int) := by
  obtain ⟨h1,h2⟩ := error_bounds i
  obtain ⟨h3,h4⟩ := error_bounds (i+len)
  obtain ⟨h5,h6⟩ := error_bounds j
  obtain ⟨h7,h8⟩ := error_bounds (j+len)
  unfold error at *
  push_cast at *
  have hlo : (-5 : Int) < (b (i+len)-b i)-(b (j+len)-b j) := by
    exact_mod_cast (show (-5 : ℝ) < ((b (i+len) : ℝ)-b i)-((b (j+len) : ℝ)-b j) by linarith)
  have hhi : (b (i+len)-b i)-(b (j+len)-b j) < (5 : Int) := by
    exact_mod_cast (show ((b (i+len) : ℝ)-b i)-((b (j+len) : ℝ)-b j) < (5 : ℝ) by linarith)
  rw [abs_le]
  omega

def globalInf : ℝ := sInf (Set.range error)
def globalSup : ℝ := sSup (Set.range error)

theorem error_bddBelow : BddBelow (Set.range error) := by
  refine ⟨-11/10,?_⟩
  rintro _ ⟨n,rfl⟩
  exact (error_bounds n).1.le

theorem error_bddAbove : BddAbove (Set.range error) := by
  refine ⟨6/5,?_⟩
  rintro _ ⟨n,rfl⟩
  exact (error_bounds n).2.le

theorem extrema_enclosure :
    -11/10 ≤ globalInf ∧ globalInf ≤ 664-Discrepancy.slope*1167 ∧
    54-Discrepancy.slope*93 ≤ globalSup ∧ globalSup ≤ 6/5 := by
  have h := Discrepancy.global_extrema_enclosure error (-11/10) (6/5)
    (664-Discrepancy.slope*1167) (54-Discrepancy.slope*93)
    (fun n => (error_bounds n).1.le) (fun n => (error_bounds n).2.le)
    1167 93 (by simp [error,b_1167]) (by simp [error,b_ninety_three])
  exact h

theorem extrema_approximable (eps : ℝ) (heps : 0 < eps) :
    (∃ n, error n < globalInf+eps) ∧ (∃ n, globalSup-eps < error n) := by
  constructor
  · have hi : globalInf < globalInf+eps := by linarith
    obtain ⟨x,hx,hlt⟩ := exists_lt_of_csInf_lt (s := Set.range error)
      (by exact ⟨error 0,⟨0,rfl⟩⟩) hi
    obtain ⟨n,rfl⟩ := hx
    exact ⟨n,hlt⟩
  · have hi : globalSup-eps < globalSup := by linarith
    obtain ⟨x,hx,hlt⟩ := exists_lt_of_lt_csSup (s := Set.range error)
      (by exact ⟨error 0,⟨0,rfl⟩⟩) hi
    obtain ⟨n,rfl⟩ := hx
    exact ⟨n,hlt⟩

#print axioms error_bounds
#print axioms four_balanced
#print axioms extrema_enclosure

end

end CloitreCollaboration.Candidate
