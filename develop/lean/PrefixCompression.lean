import GlobalConsequences
import SuffixReachability

set_option autoImplicit false

namespace CloitreCollaboration.Candidate

noncomputable section

theorem general_tail_bound (pref suf : List Bool) (hk : 3 ≤ suf.length)
    (hlegal : Greedy.BinaryAdmissible (pref++suf).reverse) :
    |contributionAt Discrepancy.slope suf.length pref| ≤
      Discrepancy.tailBound (suf.length-3) := by
  have ha := Greedy.high_positions_admissible pref suf hlegal
  have hlo : ∀ p, p ∈ Greedy.positions suf.length pref.reverse → suf.length-3+3 ≤ p := by
    intro p hp
    have := Greedy.positions_lower _ _ _ hp
    omega
  have hb := Greedy.admissible_tail_bound Discrepancy.rho Discrepancy.rho_gt_one
    Discrepancy.rho_cubic _ ha (suf.length-3) hlo
  have heq : contributionAt Discrepancy.slope suf.length pref=
      Greedy.tailSum Discrepancy.rho (Greedy.positions suf.length pref.reverse) := by
    unfold contributionAt Greedy.tailSum Discrepancy.slope
    congr 1
    apply List.map_congr_left
    intro p hp
    exact coefficient_eq_delta _ p (by have := hlo p hp; omega)
  rw [heq]
  exact hb

theorem wordValue_nonnegative (bs : List Bool) : 0 ≤ wordValue bs :=
  Greedy.value_nonneg _

theorem value_length_bound (bs : List Bool) (hlegal : Greedy.BinaryAdmissible bs.reverse) :
    wordValue bs < U bs.length := by
  have hpos := Greedy.U_pos bs.length
  unfold wordValue selected
  cases he : Greedy.positions 0 bs.reverse with
  | nil => simp [Greedy.value]; exact hpos
  | cons p ps =>
    have ha : Greedy.Admissible (p::ps) := by simpa only [Greedy.BinaryAdmissible,he] using hlegal
    have hp := Greedy.positions_upper bs.reverse 0 p (by rw [he]; simp)
    simp only [List.length_reverse, Nat.zero_add] at hp
    exact (Greedy.value_bound p ps ha).trans_le (Greedy.U_strictMono.monotone (by omega))

theorem path_error {bs : List Bool} {last : Fin 28} (hp : Suffix.Path 0 bs last) :
    error (wordValue bs).toNat=Suffix.contribution Discrepancy.slope bs+(Suffix.output last : ℝ) := by
  have hl := Suffix.initial_path_legal hp
  have hv : WordArithmetic.wordValue Greedy.bitValue bs=((wordValue bs).toNat : Int) := by
    rw [← Greedy.positions_word_value]
    exact (Int.toNat_of_nonneg (wordValue_nonnegative bs)).symm
  have hb := b_on_path (wordValue bs).toNat bs last hl hv hp
  unfold error
  rw [hb]
  have hn : (((wordValue bs).toNat : Nat) : ℝ)=(wordValue bs : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (wordValue_nonnegative bs)
  rw [hn]
  exact candidate_error _ _ _

/-- Explicit bounded-length approximation: replace the high prefix by one of 28
fixed words of length at most 13, preserving its state and all low K digits. -/
theorem finite_window_word_approximation (n K : Nat) (hK : 3 ≤ K) :
    ∃ (w : List Bool) (last : Fin 28), Suffix.Path 0 w last ∧ w.length ≤ K+13 ∧
      |error n-(Suffix.contribution Discrepancy.slope w+(Suffix.output last : ℝ))| ≤
        2*Discrepancy.tailBound (K-3) := by
  obtain ⟨bs,last,hl,hv,hp⟩ := Certificate.Identification.all_paths n
  let padded := List.replicate (K-bs.length) false++bs
  have hplen : K ≤ padded.length := by simp [padded]; omega
  have hppath : Suffix.Path 0 padded last := Suffix.path_leading_zeros hp _
  have hpvalue : wordValue padded=(n : Int) := by
    unfold wordValue
    rw [selected_leading_zeros]
    exact (Greedy.positions_word_value bs).trans hv
  let pref := padded.take (padded.length-K)
  let suf := padded.drop (padded.length-K)
  have hjoin : pref++suf=padded := List.take_append_drop _ _
  have hslen : suf.length=K := by simp [suf]; omega
  have hp' : Suffix.Path 0 (pref++suf) last := by simpa only [hjoin] using hppath
  obtain ⟨mid,_,hs⟩ := path_append hp'
  let short := Suffix.reachingPrefix mid++suf
  have hshort := (Suffix.suffix_realizable hs).1
  have hshortlegal := (Greedy.dfa_accepts_iff short).mp ((Suffix.suffix_realizable hs).2.1)
  have hshortlen : short.length ≤ K+13 := by
    have hreach := (Suffix.reaching_certificate mid).2
    simp only [short,List.length_append,hslen]
    omega
  refine ⟨short,last,hshort,hshortlen,?_⟩
  · have herror1 := path_error hppath
    rw [hpvalue] at herror1
    simp only [Int.toNat_natCast] at herror1
    rw [herror1,← hjoin,contribution_append,contribution_append]
    have ht1 := general_tail_bound pref suf (by omega)
      ((Greedy.dfa_accepts_iff _).mp (Suffix.initial_path_legal hp'))
    have ht2 := general_tail_bound (Suffix.reachingPrefix mid) suf (by omega) hshortlegal
    have heq : contributionAt Discrepancy.slope suf.length pref+
        Suffix.contribution Discrepancy.slope suf+(Suffix.output last : ℝ)-
        (contributionAt Discrepancy.slope suf.length (Suffix.reachingPrefix mid)+
        Suffix.contribution Discrepancy.slope suf+(Suffix.output last : ℝ))=
        contributionAt Discrepancy.slope suf.length pref-
        contributionAt Discrepancy.slope suf.length (Suffix.reachingPrefix mid) := by ring
    rw [heq]
    calc
      _ ≤ |contributionAt Discrepancy.slope suf.length pref|+
        |contributionAt Discrepancy.slope suf.length (Suffix.reachingPrefix mid)| := by
          simpa using abs_sub_le (contributionAt Discrepancy.slope suf.length pref) 0
            (contributionAt Discrepancy.slope suf.length (Suffix.reachingPrefix mid))
      _ ≤ Discrepancy.tailBound (suf.length-3)+Discrepancy.tailBound (suf.length-3) := add_le_add ht1 ht2
      _ = _ := by rw [hslen]; ring

theorem finite_window_approximation (n K : Nat) (hK : 3 ≤ K) :
    ∃ m : Nat, (m : Int) < U (K+13) ∧
      |error n-error m| ≤ 2*Discrepancy.tailBound (K-3) := by
  obtain ⟨w,last,hp,hlen,herr⟩ := finite_window_word_approximation n K hK
  refine ⟨(wordValue w).toNat,?_,?_⟩
  · rw [Int.toNat_of_nonneg (wordValue_nonnegative w)]
    exact (value_length_bound w ((Greedy.dfa_accepts_iff _).mp (Suffix.initial_path_legal hp))).trans_le
      (Greedy.U_strictMono.monotone hlen)
  · rwa [path_error hp]

#print axioms finite_window_approximation

end

end CloitreCollaboration.Candidate
