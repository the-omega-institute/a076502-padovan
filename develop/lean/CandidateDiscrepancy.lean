import SuffixSoundness
import GreedyRepresentation
import GreedyTail

set_option autoImplicit false

namespace CloitreCollaboration.Candidate

noncomputable section

def selected (bs : List Bool) : List Nat := Greedy.positions 0 bs.reverse
def shiftWeight (p : Nat) : Int := if 2 ≤ p then U (p-2) else 0
def shiftedValue (bs : List Bool) : Int := ((selected bs).map shiftWeight).sum
def wordValue (bs : List Bool) : Int := Greedy.value (selected bs)
def wordCandidate (bs : List Bool) (last : Fin 28) : Int := shiftedValue bs+Suffix.output last

def contributionAt (c : ℝ) (offset : Nat) (bs : List Bool) : ℝ :=
  ((Greedy.positions offset bs.reverse).map (Suffix.coefficient c)).sum

theorem contributionAt_cons (c : ℝ) (offset : Nat) (b : Bool) (bs : List Bool) :
    contributionAt c offset (b::bs) =
      (if b then Suffix.coefficient c (offset+bs.length) else 0)+contributionAt c offset bs := by
  unfold contributionAt
  rw [List.reverse_cons, Greedy.positions_append]
  cases b <;> simp [Greedy.positions]

theorem contributionAt_zero (c : ℝ) (bs : List Bool) :
    contributionAt c 0 bs=Suffix.contribution c bs := by
  induction bs with
  | nil => simp [contributionAt, Greedy.positions, Suffix.contribution]
  | cons b bs ih => rw [contributionAt_cons, ih]; simp [Suffix.contribution]

theorem contribution_append (c : ℝ) (pref suf : List Bool) :
    Suffix.contribution c (pref++suf)=
      contributionAt c suf.length pref+Suffix.contribution c suf := by
  rw [← contributionAt_zero]
  unfold contributionAt
  rw [List.reverse_append, Greedy.positions_append]
  simp only [List.length_reverse, Nat.zero_add, List.map_append, List.sum_append]
  rw [← contributionAt_zero]
  rfl

theorem selected_sum_value (ps : List Nat) :
    (ps.map (fun p => (U p : ℝ))).sum=(Greedy.value ps : ℝ) := by
  induction ps with
  | nil => simp [Greedy.value]
  | cons p ps ih => simp [Greedy.value,ih]

theorem candidate_error (c : ℝ) (bs : List Bool) (last : Fin 28) :
    (wordCandidate bs last : ℝ)-c*(wordValue bs : ℝ)=
      Suffix.contribution c bs+(Suffix.output last : ℝ) := by
  rw [← contributionAt_zero]
  unfold contributionAt wordCandidate wordValue shiftedValue selected
  push_cast
  rw [← selected_sum_value]
  have hh (ps : List Nat) : ((ps.map shiftWeight).sum : ℝ)-c*(ps.map (fun p => (U p : ℝ))).sum =
      (ps.map (Suffix.coefficient c)).sum := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add]
      have hs : (shiftWeight p : ℝ)=if 2 ≤ p then (U (p-2) : ℝ) else 0 := by
        unfold shiftWeight
        split <;> simp_all
      rw [hs]
      unfold Suffix.coefficient at *
      linear_combination ih
  have hh' := hh (Greedy.positions 0 bs.reverse)
  push_cast at hh'
  linear_combination hh'

theorem path_append {q last : Fin 28} {pref suf : List Bool}
    (hp : Suffix.Path q (pref++suf) last) :
    ∃ mid, Suffix.Path q pref mid ∧ Suffix.Path mid suf last := by
  induction pref generalizing q with
  | nil => exact ⟨q, Suffix.Path.nil q, hp⟩
  | cons b pref ih =>
    cases hp with
    | cons he hp =>
      obtain ⟨mid,hfirst,hsecond⟩ := ih hp
      exact ⟨mid,Suffix.Path.cons he hfirst,hsecond⟩

theorem contribution_leading_zeros (c : ℝ) (bs : List Bool) (k : Nat) :
    Suffix.contribution c (List.replicate k false++bs)=Suffix.contribution c bs := by
  induction k with
  | zero => simp
  | succ k ih => simpa [List.replicate_succ, Suffix.contribution] using ih

theorem selected_leading_zeros (bs : List Bool) (k : Nat) :
    selected (List.replicate k false++bs)=selected bs := by
  unfold selected
  rw [List.reverse_append, Greedy.positions_append]
  simp [Greedy.positions_false]

theorem coefficient_eq_delta (r : ℝ) (p : Nat) (hp : 3 ≤ p) :
    Suffix.coefficient ((r⁻¹)^2) p=Discrepancy.delta r (p-3) := by
  unfold Suffix.coefficient Discrepancy.delta Discrepancy.realU
  rw [if_pos (by omega : 2 ≤ p)]
  rw [show p-3+1=p-2 by omega, show p-3+3=p by omega]

theorem contribution_tail_bound (r : ℝ) (hr : 1 < r) (hc : r^3=r+1)
    (pref suf : List Bool) (hlen : suf.length=20)
    (hlegal : Greedy.BinaryAdmissible (pref++suf).reverse) :
    |contributionAt ((r⁻¹)^2) 20 pref| ≤ Discrepancy.tailBound 17 := by
  have ha := Greedy.high_positions_admissible pref suf hlegal
  rw [hlen] at ha
  have hlo : ∀ p, p ∈ Greedy.positions 20 pref.reverse → 17+3 ≤ p := by
    intro p hp
    exact Greedy.positions_lower _ _ _ hp
  have hb := Greedy.admissible_tail_bound r hr hc _ ha 17 hlo
  have heq : contributionAt ((r⁻¹)^2) 20 pref=
      Greedy.tailSum r (Greedy.positions 20 pref.reverse) := by
    unfold contributionAt Greedy.tailSum
    congr 1
    apply List.map_congr_left
    intro p hp
    exact coefficient_eq_delta r p (by have := hlo p hp; omega)
  rw [heq]
  exact hb

theorem long_word_sharp_error (r : ℝ) (hr : 1 < r) (hc : r^3=r+1)
    (bs : List Bool) (last : Fin 28) (hlen : 20 ≤ bs.length)
    (hlegal : Greedy.BinaryAdmissible bs.reverse) (hpath : Suffix.Path 0 bs last) :
    -11/10 < (wordCandidate bs last : ℝ)-(r⁻¹)^2*(wordValue bs : ℝ) ∧
      (wordCandidate bs last : ℝ)-(r⁻¹)^2*(wordValue bs : ℝ) < 6/5 := by
  let pref := bs.take (bs.length-20)
  let suf := bs.drop (bs.length-20)
  have hjoin : pref++suf=bs := List.take_append_drop _ _
  have hslen : suf.length=20 := by simp [suf]; omega
  have hcub := Discrepancy.coefficient_cubic r (by linarith) hc
  have hrough := Discrepancy.inverse_square_bounds r hr hc
  obtain ⟨cl,cu⟩ := Discrepancy.coefficient_bracket ((r⁻¹)^2)
    (by linarith [hrough.1]) (by linarith [hrough.2]) hcub
  have hpath' : Suffix.Path 0 (pref++suf) last := by simpa only [hjoin] using hpath
  obtain ⟨mid,_,hps⟩ := path_append hpath'
  have ht := contribution_tail_bound r hr hc pref suf hslen (by simpa only [hjoin] using hlegal)
  have hb := Suffix.suffix_tail_sharp ((r⁻¹)^2) (contributionAt ((r⁻¹)^2) 20 pref)
    cl.le cu.le hps hslen ht
  rw [candidate_error, ← hjoin, contribution_append, hslen]
  exact hb

/-- Every greedy E-path has corrected floor offsets, with no tail premise. -/
theorem word_sharp_error (r : ℝ) (hr : 1 < r) (hc : r^3=r+1)
    (bs : List Bool) (last : Fin 28)
    (hlegal : Greedy.BinaryAdmissible bs.reverse) (hpath : Suffix.Path 0 bs last) :
    -11/10 < (wordCandidate bs last : ℝ)-(r⁻¹)^2*(wordValue bs : ℝ) ∧
      (wordCandidate bs last : ℝ)-(r⁻¹)^2*(wordValue bs : ℝ) < 6/5 := by
  let padded := List.replicate (20-bs.length) false++bs
  have hsel : selected padded=selected bs := selected_leading_zeros _ _
  have hlen : 20 ≤ padded.length := by simp [padded]; omega
  have hpadlegal : Greedy.BinaryAdmissible padded.reverse := by
    change Greedy.Admissible (selected padded)
    rw [hsel]
    exact hlegal
  have hpadpath : Suffix.Path 0 padded last := Suffix.path_leading_zeros hpath _
  have hb := long_word_sharp_error r hr hc padded last hlen hpadlegal hpadpath
  simpa only [wordCandidate, shiftedValue, wordValue, hsel] using hb

theorem word_error (r : ℝ) (hr : 1 < r) (hc : r^3=r+1)
    (bs : List Bool) (last : Fin 28)
    (hlegal : Greedy.BinaryAdmissible bs.reverse) (hpath : Suffix.Path 0 bs last) :
    -2 < (wordCandidate bs last : ℝ)-(r⁻¹)^2*(wordValue bs : ℝ) ∧
      (wordCandidate bs last : ℝ)-(r⁻¹)^2*(wordValue bs : ℝ) < 2 := by
  obtain ⟨hl,hu⟩ := word_sharp_error r hr hc bs last hlegal hpath
  constructor <;> linarith

theorem word_floor_offsets (r : ℝ) (hr : 1 < r) (hc : r^3=r+1)
    (bs : List Bool) (last : Fin 28)
    (hlegal : Greedy.BinaryAdmissible bs.reverse) (hpath : Suffix.Path 0 bs last) :
    wordCandidate bs last-⌊(r⁻¹)^2*(wordValue bs : ℝ)⌋ ∈ ({-1,0,1,2} : Finset Int) := by
  obtain ⟨hl,hu⟩ := word_error r hr hc bs last hlegal hpath
  exact Discrepancy.floor_offsets _ _ hl hu

#print axioms word_error
#print axioms word_floor_offsets

end

end CloitreCollaboration.Candidate
