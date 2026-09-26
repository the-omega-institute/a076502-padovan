import TightSuffixSoundness
import FinalIdentification

set_option autoImplicit false

namespace CloitreCollaboration.Candidate

theorem tight_error_bound (n : Nat) :
    -1049234/1000000 < error n ∧ error n < 1155081/1000000 := by
  obtain ⟨bs,last,hl,hv,hp⟩ := Certificate.Identification.all_paths n
  let padded := List.replicate (105-bs.length) false++bs
  have hplen : 105 ≤ padded.length := by simp [padded]; omega
  have hppath : Suffix.Path 0 padded last := Suffix.path_leading_zeros hp _
  have hpvalue : wordValue padded=(n : Int) := by
    unfold wordValue
    rw [selected_leading_zeros]
    exact (Greedy.positions_word_value bs).trans hv
  let pref := padded.take (padded.length-105)
  let suf := padded.drop (padded.length-105)
  have hjoin : pref++suf=padded := List.take_append_drop _ _
  have hslen : suf.length=105 := by simp [suf]; omega
  have hp' : Suffix.Path 0 (pref++suf) last := by simpa only [hjoin] using hppath
  obtain ⟨mid,_,hs⟩ := path_append hp'
  have ht := general_tail_bound pref suf (by omega)
    ((Greedy.dfa_accepts_iff _).mp (Suffix.initial_path_legal hp'))
  rw [hslen] at ht
  have hb := TightSuffix.suffix_tail_bound (contributionAt Discrepancy.slope 105 pref) hs hslen ht
  have he := path_error hppath
  rw [hpvalue] at he
  simp only [Int.toNat_natCast] at he
  rw [he,←hjoin,contribution_append,hslen]
  exact hb

#print axioms tight_error_bound

end CloitreCollaboration.Candidate

namespace CloitreCollaboration.Certificate.Identification

/-- The six-decimal bounds stated in the paper, now closed in the kernel. -/
theorem sequence_tight_discrepancy (a : Nat → Nat) (h0 : a 0=0) (h1 : a 1=1)
    (ha : NestedRecurrence a) (n : Nat) :
    -1049234/1000000 < (a n : ℝ)-Discrepancy.slope*n ∧
      (a n : ℝ)-Discrepancy.slope*n < 1155081/1000000 := by
  rw [sequence_identification a h0 h1 ha]
  have h := Candidate.tight_error_bound n
  unfold Candidate.error at h
  rw [←bNat_cast n] at h
  exact_mod_cast h

#print axioms sequence_tight_discrepancy

end CloitreCollaboration.Certificate.Identification
