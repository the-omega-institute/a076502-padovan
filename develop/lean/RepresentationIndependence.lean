import GreedyRepresentation
import WordArithmetic

set_option autoImplicit false

namespace CloitreCollaboration.Greedy

open WordArithmetic

theorem positions_weighted (weights : Nat -> Int) (digits : List Bool) (k : Nat) :
    ((positions k digits).map weights).sum = weighted weights k (digits.map bitValue) := by
  induction digits generalizing k with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simp [positions, ih, bitValue, weighted, Int.add_comm]

def shiftedWeight (p : Nat) : Int := if 2 <= p then U (p - 2) else 0

theorem weighted_shift_offset (digits : List Int) (k : Nat) :
    weighted shiftedWeight (k + 2) digits = weighted U k digits := by
  induction digits generalizing k with
  | nil => rfl
  | cons a digits ih =>
      simp only [weighted]
      have hk : k + 2 + 1 = (k + 1) + 2 := by omega
      rw [hk, ih]
      simp [shiftedWeight]

theorem weighted_shift_drop (digits : List Int) :
    weighted shiftedWeight 0 digits = weighted U 0 (digits.drop 2) := by
  rcases digits with _ | ⟨a, _ | ⟨b, digits⟩⟩
  · rfl
  · simp [weighted, shiftedWeight]
  · simpa [weighted, shiftedWeight] using weighted_shift_offset digits 0

/-- Shared bridge from the selected-position candidate to the delayed-carry candidate. -/
theorem positions_shift_value (bs : List Bool) :
    ((positions 0 bs.reverse).map (fun p => if 2 <= p then U (p - 2) else 0)).sum =
      shiftValue bitValue bs := by
  change ((positions 0 bs.reverse).map shiftedWeight).sum = _
  rw [positions_weighted, weighted_shift_drop]
  simp only [shiftValue, List.map_drop]

theorem positions_word_value (bs : List Bool) :
    value (positions 0 bs.reverse) = wordValue bitValue bs := positions_value bs.reverse 0

theorem wordValue_leading_zero (bs : List Bool) :
    wordValue bitValue (false :: bs) = wordValue bitValue bs := by
  unfold wordValue
  rw [List.reverse_cons, List.map_append, WordArithmetic.weighted_append]
  simp [bitValue, weighted]

theorem shiftValue_leading_zero (bs : List Bool) :
    shiftValue bitValue (false :: bs) = shiftValue bitValue bs := by
  unfold shiftValue
  rw [List.reverse_cons, List.drop_append, List.map_append, WordArithmetic.weighted_append]
  have hz (n k : Nat) : weighted U k (([false].drop n).map bitValue) = 0 := by
    cases n <;> simp [bitValue, weighted]
  rw [hz]
  omega

def pad (n : Nat) (bs : List Bool) : List Bool := List.replicate n false ++ bs

theorem pad_length (n : Nat) (bs : List Bool) : (pad n bs).length = n + bs.length := by
  simp [pad]

theorem pad_accepts (n : Nat) (bs : List Bool) : AcceptsFrom 4 (pad n bs) <-> AcceptsFrom 4 bs := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change AcceptsFrom 4 (false :: pad n bs) <-> _
      rw [leading_zero_acceptance, ih]

theorem pad_value (n : Nat) (bs : List Bool) : wordValue bitValue (pad n bs) = wordValue bitValue bs := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change wordValue bitValue (false :: pad n bs) = _
      rw [wordValue_leading_zero, ih]

theorem pad_shift (n : Nat) (bs : List Bool) : shiftValue bitValue (pad n bs) = shiftValue bitValue bs := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change shiftValue bitValue (false :: pad n bs) = _
      rw [shiftValue_leading_zero, ih]

theorem pad_output (e : List Bool -> Int) (he : forall bs, e (false :: bs) = e bs)
    (n : Nat) (bs : List Bool) : e (pad n bs) = e bs := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change e (false :: pad n bs) = _
      rw [he, ih]

theorem equal_value_equal_padding (bs cs : List Bool)
    (hb : AcceptsFrom 4 bs) (hc : AcceptsFrom 4 cs)
    (hv : wordValue bitValue bs = wordValue bitValue cs) :
    pad cs.length bs = pad bs.length cs := by
  have hb' := (dfa_accepts_iff _).mp ((pad_accepts cs.length bs).mpr hb)
  have hc' := (dfa_accepts_iff _).mp ((pad_accepts bs.length cs).mpr hc)
  have hrev := binary_unique_of_length (pad cs.length bs).reverse (pad bs.length cs).reverse
    hb' hc' (by simp [pad_length]; omega) (by
      change wordValue bitValue (pad cs.length bs) = wordValue bitValue (pad bs.length cs)
      rwa [pad_value, pad_value])
  exact List.reverse_injective hrev

/-- The Padovan shift plus any zero-padding-invariant output is representation-independent. -/
theorem candidate_representation_independent (e : List Bool -> Int)
    (he : forall bs, e (false :: bs) = e bs) (bs cs : List Bool)
    (hb : AcceptsFrom 4 bs) (hc : AcceptsFrom 4 cs)
    (hv : wordValue bitValue bs = wordValue bitValue cs) :
    shiftValue bitValue bs + e bs = shiftValue bitValue cs + e cs := by
  have hp := equal_value_equal_padding bs cs hb hc hv
  calc
    _ = shiftValue bitValue (pad cs.length bs) + e (pad cs.length bs) := by
      rw [pad_shift, pad_output e he]
    _ = shiftValue bitValue (pad bs.length cs) + e (pad bs.length cs) := by rw [hp]
    _ = _ := by rw [pad_shift, pad_output e he]

#print axioms candidate_representation_independent

end CloitreCollaboration.Greedy
