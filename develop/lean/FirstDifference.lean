import FinalIdentification
import Generated.DifferenceTrace
import Generated.TotalDifference

set_option autoImplicit false

namespace CloitreCollaboration.Certificate.Difference

open Primitive Operations WordArithmetic Identification CloitreCollaboration.Certificate.Composition

theorem next_value (w : List (Fin 4)) (hw : accepts NextB w) :
    bInt (val 1 w + 1) = val 0 w := by
  obtain ⟨u,rfl,hu⟩ := NextBSound w hw
  have hs := successor_value adderValue Constants.one_value _ (NextBProductPart0Sound u hu)
  have hg := graph_candidate _ (NextBProductPart1Sound u hu)
  change bInt (val 1 _) = val 0 _ at hg
  have m1 := val_map NextBProductPart0Letter 1 2 (by decide) u
  have m2 := val_map NextBProductPart0Letter 0 1 (by decide) u
  have m3 := val_map NextBProductPart1Letter 1 2 (by decide) u
  have m4 := val_map NextBProductPart1Letter 0 0 (by decide) u
  rw [m1,m2] at hs
  rw [m3,m4] at hg
  rw [val_map NextBLetter 1 1 (by decide),val_map NextBLetter 0 0 (by decide)]
  have he : val 1 u+1 = val 2 u := by omega
  rw [he]
  exact hg

theorem difference_value (w : List (Fin 2)) (hw : accepts Operations.Difference w) :
    bInt (val 0 w + 1)-bInt (val 0 w) = dOutput (dRun 0 (w.map (bit 0))) := by
  obtain ⟨u,rfl,hu⟩ := DifferenceSound w hw
  have hg := graph_candidate _ (DifferenceProductPart0Sound u hu)
  change bInt (val 1 _) = val 0 _ at hg
  have hn := next_value _ (DifferenceProductPart1Sound u hu)
  have hd := differenceValue _ (DifferenceProductPart2Sound u hu)
  change val 0 _ = _ at hd
  have ha := adderValue _ (DifferenceProductPart3Sound u hu)
  change val 2 _ + val 1 _ = val 0 _ at ha
  rw [val_map DifferenceProductPart0Letter 1 3 (by decide),
      val_map DifferenceProductPart0Letter 0 2 (by decide)] at hg
  rw [val_map DifferenceProductPart1Letter 1 3 (by decide),
      val_map DifferenceProductPart1Letter 0 1 (by decide)] at hn
  rw [val_map DifferenceProductPart2Letter 0 0 (by decide)] at hd
  rw [val_map DifferenceProductPart3Letter 2 2 (by decide),
      val_map DifferenceProductPart3Letter 1 0 (by decide),
      val_map DifferenceProductPart3Letter 0 1 (by decide)] at ha
  have hdigit : ∀ a : Fin 16, bit 1 (DifferenceProductPart2Letter a) = bit 3 a := by decide
  simp only [List.map_map,Function.comp_def,hdigit] at hd
  rw [val_map DifferenceLetter 0 3 (by decide)]
  have hdigit' : ∀ a : Fin 16, bit 0 (DifferenceLetter a) = bit 3 a := by decide
  simp only [List.map_map,Function.comp_def,hdigit']
  omega

theorem difference_at_word (bs : List Bool) (hl : Greedy.AcceptsFrom 4 bs) (n : Nat)
    (hv : wordValue Greedy.bitValue bs = (n : Int)) :
    Candidate.b (n+1)-Candidate.b n = dOutput (dRun 0 bs) := by
  have hp := Domains.graph_domain bs hl
  have hd := difference_value _ (totalDifference _ hp)
  have hvp : val 0 ([0,0,0] ++ bs.map Domains.symbol) = (n : Int) :=
    (Domains.padded_symbols_value bs).trans hv
  rw [hvp] at hd
  have he : ∀ b, bit 0 (Domains.symbol b) = b := by decide
  have hz : dStep 0 false = 0 := by decide
  have hinput : ([0,0,0] ++ bs.map Domains.symbol).map (bit 0) = [false,false,false] ++ bs := by
    simp only [List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,he]
    simp only [List.map_id_fun']
    rfl
  rw [hinput] at hd
  simpa [bInt,dRun,List.foldl_cons,hz] using hd

theorem sequence_first_difference (a : Nat → Nat) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (ha : NestedRecurrence a) (n : Nat) :
    (a (n+1) : Int)-(a n : Int) = dOutput (dRun 0 (Candidate.representation n)) := by
  rw [sequence_identification a h0 h1 ha,bNat_cast,bNat_cast]
  exact difference_at_word _ (Candidate.representation_legal n) n (Candidate.representation_value n)

#print axioms sequence_first_difference

end CloitreCollaboration.Certificate.Difference
