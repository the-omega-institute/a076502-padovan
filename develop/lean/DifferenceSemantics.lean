import ConstantSemantics
import GraphCandidate
import Generated.DifferenceData

set_option autoImplicit false

namespace CloitreCollaboration.Certificate.Difference

open Primitive WordArithmetic Operations

def smallStep (s : Fin 3) (a : Fin 4) : Fin 3 :=
  if s = 0 then if bit 0 a then 1 else 0 else 2

def dStep (q : Fin 28) (b : Bool) : Fin 28 := Fin.ofNat 28 (dTransitions q b).toNat

def dRun (q : Fin 28) (w : List Bool) : Fin 28 := w.foldl dStep q

def diffStep (s : Fin 28 × Fin 3) (a : Fin 4) : Fin 28 × Fin 3 :=
  (dStep s.1 (bit 1 a), smallStep s.2 a)

def diffGood (s : Fin 28 × Fin 3) : Bool :=
  decide (s.2.val < 2 ∧ dOutput s.1 = (s.2.val : Int))

theorem small_sink (w : List (Fin 4)) : w.foldl smallStep 2 = 2 := by
  induction w with
  | nil => rfl
  | cons a w ih => exact ih

theorem small_terminal (w : List (Fin 4))
    (h : (w.foldl smallStep 1).val < 2) : w = [] := by
  cases w with
  | nil => rfl
  | cons a w =>
    change (w.foldl smallStep 2).val < 2 at h
    rw [small_sink] at h
    contradiction

theorem small_value (w : List (Fin 4)) (h : (w.foldl smallStep 0).val < 2) :
    wordValue (digit 0) w = ((w.foldl smallStep 0).val : Int) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    by_cases hb : bit 0 a = true
    · have hs : smallStep 0 a = 1 := by simp [smallStep,hb]
      have hn := small_terminal w (by simpa only [List.foldl_cons,hs] using h)
      subst w
      have hd : digit 0 a = 1 := by
        have := Identification.bool_digit 0 a
        simpa [hb,Greedy.bitValue] using this.symm
      simp [wordValue,weighted,U,hd,List.foldl_cons,hs]
    · have hs : smallStep 0 a = 0 := by simp [smallStep,hb]
      have hd : digit 0 a = 0 := by
        have := Identification.bool_digit 0 a
        simpa [hb,Greedy.bitValue] using this.symm
      rw [Constants.wordValue_zero_cons _ _ _ hd]
      simpa only [List.foldl_cons,hs] using ih (by simpa only [List.foldl_cons,hs] using h)

theorem diff_fold (w : List (Fin 4)) (s : Fin 28 × Fin 3) :
    w.foldl diffStep s = (dRun s.1 (w.map (bit 1)),w.foldl smallStep s.2) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => simpa only [List.foldl_cons,List.map_cons,diffStep,dRun] using ih (diffStep s a)

theorem diff_trace_value (w : List (Fin 4))
    (h : diffGood (w.foldl diffStep (0,0)) = true) :
    wordValue (digit 0) w = dOutput (dRun 0 (w.map (bit 1))) := by
  rw [diff_fold] at h
  simp only [diffGood,decide_eq_true_eq] at h
  exact (small_value w h.1).trans h.2.symm

end CloitreCollaboration.Certificate.Difference
