import CanonicalCandidate
import Domains
import Generated.GraphTrace
import Generated.TotalGraph

set_option autoImplicit false

namespace CloitreCollaboration.Certificate.Identification

open Primitive Operations WordArithmetic

theorem bool_digit {k : Nat} (i : Nat) (a : Fin k) :
    Greedy.bitValue (bit i a) = digit i a := by
  have h : a.val / 2^i % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold Greedy.bitValue bit digit
  split <;> simp_all <;> omega

theorem bool_value {k : Nat} (i : Nat) (w : List (Fin k)) :
    wordValue Greedy.bitValue (w.map (bit i)) = wordValue (digit i) w := by
  simp only [wordValue, ← List.map_reverse, List.map_map, Function.comp_def, bool_digit]

theorem bool_shift {k : Nat} (i : Nat) (w : List (Fin k)) :
    shiftValue Greedy.bitValue (w.map (bit i)) = shiftValue (digit i) w := by
  simp only [shiftValue, ← List.map_reverse, ← List.map_drop, List.map_map,
    Function.comp_def, bool_digit]

theorem word_nonneg {k : Nat} (i : Nat) (w : List (Fin k)) :
    0 ≤ wordValue (digit i) w := by
  rw [← bool_value, ← Greedy.positions_word_value]
  exact Greedy.value_nonneg _

theorem greedy_run (q : Fin 7) (w : List (Fin 2)) :
    run greedyMachine q w = Greedy.dfaRun q (w.map (bit 0)) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => exact ih _

theorem greedy_accepts (w : List (Fin 2)) (h : accepts greedyMachine w) :
    Greedy.AcceptsFrom 4 (w.map (bit 0)) := by
  unfold accepts at h
  rw [greedy_run] at h
  change (Greedy.dfaRun 4 (w.map (bit 0))).val < 6
  change (Greedy.dfaRun 4 (w.map (bit 0)) != 6) = true at h
  simp only [bne_iff_ne, ne_eq, Fin.ext_iff] at h
  have := (Greedy.dfaRun 4 (w.map (bit 0))).isLt
  omega

theorem graph_input_legal (w : List (Fin 4)) (h : accepts Graph w) :
    Greedy.AcceptsFrom 4 (w.map (bit 1)) := by
  have hg := greedy_accepts _ (graphGreedy1Sound w h)
  have he : ∀ a : Fin 4, bit 0 (graphGreedy1Letter a) = bit 1 a := by decide
  simpa only [List.map_map, Function.comp_def, he] using hg

noncomputable def bInt (n : Int) : Int := Candidate.b n.toNat

theorem graph_candidate (w : List (Fin 4)) (h : accepts Graph w) :
    bInt (wordValue (digit 1) w) = wordValue (digit 0) w := by
  have hl := graph_input_legal w h
  have hv : wordValue Greedy.bitValue (w.map (bit 1)) =
      ((wordValue (digit 1) w).toNat : Int) := by
    rw [bool_value, Int.toNat_of_nonneg (word_nonneg 1 w)]
  have hb := Candidate.b_on_word _ _ hl hv
  rw [bool_shift] at hb
  exact hb.trans (graphValue w h).symm

theorem all_graph_values (n : Nat) : ∃ w : List (Fin 4),
    accepts Graph w ∧ wordValue (digit 1) w = (n : Int) := by
  obtain ⟨v,hv,hval⟩ := Domains.every_nat_graph_domain n
  obtain ⟨w,hw,hg⟩ := GraphDomainSound v (totalGraph v hv)
  refine ⟨w,hg,?_⟩
  have he : ∀ a : Fin 4, digit 0 (GraphDomainLetter a) = digit 1 a := by decide
  rw [← hw] at hval
  simpa only [wordValue, ← List.map_reverse, List.map_map, Function.comp_def, he] using hval

theorem all_paths (n : Nat) : ∃ bs last, Greedy.AcceptsFrom 4 bs ∧
    wordValue Greedy.bitValue bs = (n : Int) ∧ Suffix.Path 0 bs last := by
  obtain ⟨w,hw,hv⟩ := all_graph_values n
  obtain ⟨last,hp⟩ := graphPath w hw
  exact ⟨w.map (bit 1),last,graph_input_legal w hw,(bool_value 1 w).trans hv,hp⟩

theorem b_nonneg (n : Nat) : 0 ≤ Candidate.b n := by
  obtain ⟨w,hw,hv⟩ := all_graph_values n
  have hb := graph_candidate w hw
  rw [hv] at hb
  change Candidate.b n = _ at hb
  rw [hb]
  exact word_nonneg 0 w

theorem candidate_discrepancy (n : Nat) :
    -2 < (Candidate.b n : ℝ)-Discrepancy.slope*n ∧
      (Candidate.b n : ℝ)-Discrepancy.slope*n < 2 := by
  obtain ⟨bs,last,hl,hv,hp⟩ := all_paths n
  exact Candidate.b_discrepancy n bs last hl hv hp

theorem candidate_offsets (n : Nat) :
    Candidate.b n - ⌊Discrepancy.slope*n⌋ ∈ ({-1,0,1,2} : Finset Int) := by
  obtain ⟨bs,last,hl,hv,hp⟩ := all_paths n
  exact Candidate.b_offsets n bs last hl hv hp

theorem candidate_limit : Filter.Tendsto (fun n : Nat => (Candidate.b n : ℝ)/n)
    Filter.atTop (nhds Discrepancy.slope) := Candidate.b_limit all_paths

#print axioms graph_candidate
#print axioms candidate_discrepancy
#print axioms candidate_offsets
#print axioms candidate_limit

end CloitreCollaboration.Certificate.Identification
