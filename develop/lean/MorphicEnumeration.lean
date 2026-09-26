import Morphic
import DifferenceSemantics

set_option autoImplicit false

namespace CloitreCollaboration.Morphic

open Certificate.Difference Certificate.Operations WordArithmetic

def languageState (q : Fin 28) : Fin 7 :=
  match q.val with
  | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | 6 => 5
  | 7 => 4 | 8 => 0 | 9 => 4 | 10 => 0 | 11 => 1 | 12 => 0 | 13 => 1
  | 14 => 2 | 15 => 1 | 16 => 2 | 17 => 3 | 18 => 2 | 19 => 3 | 20 => 4
  | 21 => 5 | 22 => 3 | 23 => 4 | 24 => 4 | 25 => 4 | 26 => 4 | 27 => 0
  | _ => 6

theorem languageState_valid : forall q : Fin 28, (languageState q).val < 6 := by decide

theorem language_step : forall (q : Fin 28) (b : Bool),
    (Greedy.dfaStep (languageState q) b).val < 6 ->
      languageState (dStep q b) = Greedy.dfaStep (languageState q) b := by decide

theorem mu_children : forall q : Fin 28, mu q =
    (if (Greedy.dfaStep (languageState q) false).val < 6 then [dStep q false] else []) ++
    (if (Greedy.dfaStep (languageState q) true).val < 6 then [dStep q true] else []) := by decide

theorem output_matches_D : forall q : Fin 28, Greedy.bitValue (output q) = dOutput q := by decide

def count (q : Fin 7) : Nat -> Nat
  | 0 => if q.val < 6 then 1 else 0
  | n + 1 => count (Greedy.dfaStep q false) n + count (Greedy.dfaStep q true) n

theorem count_sink (n : Nat) : count 6 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change count 6 n + count 6 n = 0
      omega

theorem count_terminal (n : Nat) : count 5 (n + 1) = 0 := by
  change count 6 n + count 6 n = 0
  rw [count_sink]

theorem count_rec (n : Nat) : count 4 (n + 6) = count 4 (n + 5) + count 4 (n + 1) := by
  have h4 (m : Nat) : count 4 (m+1) = count 4 m + count 0 m := rfl
  have h0 (m : Nat) : count 0 (m+1) = count 1 m := by change count 1 m + count 6 m = _; rw [count_sink]; omega
  have h1 (m : Nat) : count 1 (m+1) = count 2 m := by change count 2 m + count 6 m = _; rw [count_sink]; omega
  have h2 (m : Nat) : count 2 (m+1) = count 3 m := by change count 3 m + count 6 m = _; rw [count_sink]; omega
  have h3 (m : Nat) : count 3 (m+1) = count 4 m + count 5 m := rfl
  rw [h4 (n+5), h0 (n+4), h1 (n+3), h2 (n+2), h3 (n+1), count_terminal]
  omega

theorem count_root (n : Nat) : (count 4 n : Int) = U n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | _ | _ | _ | n
      all_goals try rfl
      rw [count_rec, Int.natCast_add, ih (n+5) (by omega), ih (n+1) (by omega), Greedy.U_step_gap]

theorem descendants_split (q : Fin 28) (n : Nat) :
    iterate mu (n+1) [q] =
      (if (Greedy.dfaStep (languageState q) false).val < 6 then iterate mu n [dStep q false] else []) ++
      (if (Greedy.dfaStep (languageState q) true).val < 6 then iterate mu n [dStep q true] else []) := by
  rw [iterate_succ_right]
  rw [show expand mu [q] = mu q by simp [expand]]
  rw [mu_children, iterate_append]
  have hnil : iterate mu n [] = [] := by
    induction n with
    | zero => rfl
    | succ n ih => simp [iterate, ih, expand]
  split_ifs <;> simp [hnil]

theorem descendants_length (q : Fin 28) (n : Nat) :
    (iterate mu n [q]).length = count (languageState q) n := by
  induction n generalizing q with
  | zero => simp [iterate, count, languageState_valid]
  | succ n ih =>
      rw [descendants_split]
      simp only [List.length_append, count]
      by_cases h0 : (Greedy.dfaStep (languageState q) false).val < 6
      · by_cases h1 : (Greedy.dfaStep (languageState q) true).val < 6
        · simp only [if_pos h0, if_pos h1, ih, language_step q false h0, language_step q true h1]
        · have he : Greedy.dfaStep (languageState q) true = 6 := by
            apply Fin.ext
            have := (Greedy.dfaStep (languageState q) true).isLt
            change _ = 6
            omega
          rw [if_pos h0, if_neg h1]
          simp only [ih, language_step q false h0, he, count_sink, List.length_nil]
      · have he : Greedy.dfaStep (languageState q) false = 6 := by
          apply Fin.ext
          have := (Greedy.dfaStep (languageState q) false).isLt
          change _ = 6
          omega
        by_cases h1 : (Greedy.dfaStep (languageState q) true).val < 6
        · rw [if_neg h0, if_pos h1]
          simp only [ih, language_step q true h1, he, count_sink, List.length_nil]
        · have he1 : Greedy.dfaStep (languageState q) true = 6 := by
            apply Fin.ext
            have := (Greedy.dfaStep (languageState q) true).isLt
            change _ = 6
            omega
          rw [if_neg h0, if_neg h1]
          simp only [he, he1, count_sink, List.length_nil]

theorem wordValue_nonneg (bs : List Bool) : 0 <= wordValue Greedy.bitValue bs := by
  rw [← Greedy.positions_word_value]
  exact Greedy.value_nonneg _

theorem wordValue_cons (b : Bool) (bs : List Bool) :
    wordValue Greedy.bitValue (b :: bs) =
      (if b then U bs.length else 0) + wordValue Greedy.bitValue bs := by
  rw [← Greedy.positions_word_value, ← Greedy.positions_word_value]
  change Greedy.value (Greedy.msPositions (b :: bs)) = _
  rw [Greedy.msPositions_cons, Greedy.value_append]
  cases b <;> simp [Greedy.value, Greedy.msPositions]

def rank (bs : List Bool) : Nat := (wordValue Greedy.bitValue bs).toNat

theorem rank_false (bs : List Bool) : rank (false :: bs) = rank bs := by
  simp [rank, wordValue_cons]

theorem rank_true (bs : List Bool) : rank (true :: bs) = (U bs.length).toNat + rank bs := by
  simp only [rank, wordValue_cons, if_true]
  exact Int.toNat_add (Greedy.U_pos bs.length).le (wordValue_nonneg bs)

theorem count_root_nat (n : Nat) : count 4 n = (U n).toNat := by
  have := congrArg Int.toNat (count_root n)
  simpa using this

theorem accepting_step {q : Fin 7} {b : Bool} {bs : List Bool}
    (h : Greedy.AcceptsFrom q (b :: bs)) : (Greedy.dfaStep q b).val < 6 := by
  by_contra hn
  have heq : Greedy.dfaStep q b = 6 := by
    apply Fin.ext
    have := (Greedy.dfaStep q b).isLt
    change _ = 6
    omega
  change Greedy.AcceptsFrom (Greedy.dfaStep q b) bs at h
  rw [heq] at h
  exact Greedy.rejects_sink bs h

theorem true_preceding : forall q : Fin 28,
    (Greedy.dfaStep (languageState q) true).val < 6 ->
      Greedy.dfaStep (languageState q) false = 4 := by decide

theorem nth_append_left {A : Type} [Inhabited A] (xs ys : List A) (i : Nat)
    (hi : i < xs.length) : (xs ++ ys)[i]! = xs[i]! := by
  have ht : i < (xs ++ ys).length := by simp; omega
  simp only [getElem!_pos, hi, ht]
  exact List.getElem_append_left hi

theorem nth_append_right {A : Type} [Inhabited A] (xs ys : List A) (i : Nat)
    (hi : i < ys.length) : (xs ++ ys)[xs.length + i]! = ys[i]! := by
  have ht : xs.length + i < (xs ++ ys).length := by simp; omega
  simp only [getElem!_pos, hi, ht]
  rw [List.getElem_append_right (by omega)]
  simp

/-- Numeric value is the exact index in the lexicographically ordered padded tree. -/
theorem descendants_rank (bs : List Bool) (q : Fin 28)
    (hlegal : Greedy.AcceptsFrom (languageState q) bs) :
    rank bs < (iterate mu bs.length [q]).length /\
      (iterate mu bs.length [q])[rank bs]! = dRun q bs := by
  induction bs generalizing q with
  | nil => exact ⟨by change 0 < 1; decide, rfl⟩
  | cons b bs ih =>
      have hb := accepting_step hlegal
      have htail : Greedy.AcceptsFrom (languageState (dStep q b)) bs := by
        rw [language_step q b hb]
        exact hlegal
      obtain ⟨hib, hiv⟩ := ih (dStep q b) htail
      change rank (b :: bs) < (iterate mu (bs.length + 1) [q]).length /\
        (iterate mu (bs.length + 1) [q])[rank (b :: bs)]! = dRun (dStep q b) bs
      rw [descendants_split]
      cases b with
      | false =>
          rw [if_pos hb, rank_false]
          constructor
          · simp only [List.length_append]; omega
          · rw [nth_append_left _ _ _ hib]
            exact hiv
      | true =>
          have hz := true_preceding q hb
          have hzero : (Greedy.dfaStep (languageState q) false).val < 6 := by rw [hz]; decide
          have hlen : (iterate mu bs.length [dStep q false]).length = (U bs.length).toNat := by
            rw [descendants_length, language_step q false hzero, hz, count_root_nat]
          rw [if_pos hzero, if_pos hb, rank_true, ← hlen]
          constructor
          · simp only [List.length_append]; omega
          · rw [nth_append_right _ _ _ hib]
            exact hiv

theorem nth_map {A B : Type} [Inhabited A] [Inhabited B] (f : A -> B)
    (xs : List A) (i : Nat) (hi : i < xs.length) : (xs.map f)[i]! = f (xs[i]!) := by
  have hm : i < (xs.map f).length := by simpa using hi
  simp only [getElem!_pos, hi, hm, List.getElem_map]

/-- The genuine infinite morphic output equals the D-DFAO on every greedy representation. -/
theorem morphicWord_at_rep (bs : List Bool) (hlegal : Greedy.AcceptsFrom 4 bs) (n : Nat)
    (hvalue : wordValue Greedy.bitValue bs = (n : Int)) :
    Greedy.bitValue (morphicWord n) = dOutput (dRun 0 bs) := by
  have hpad : Greedy.AcceptsFrom (languageState 0) (false :: bs) := hlegal
  obtain ⟨hb, hv⟩ := descendants_rank (false :: bs) 0 hpad
  have hr : rank (false :: bs) = n := by
    rw [rank_false]
    unfold rank
    rw [hvalue]
    rfl
  rw [hr] at hb hv
  simp only [List.length_cons] at hb hv
  have hm := morphicWord_erasing_prefix bs.length n hb
  rw [nth_map _ _ _ hb] at hm
  change (iterate mu (bs.length+1) [0])[n]! = dRun 0 bs at hv
  rw [hv] at hm
  rw [hm, output_matches_D]

#print axioms descendants_rank
#print axioms count_root
#print axioms morphicWord_at_rep

end CloitreCollaboration.Morphic
