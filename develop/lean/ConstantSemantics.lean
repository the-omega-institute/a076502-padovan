import PrimitiveSemantics
import Generated.One

set_option autoImplicit false

namespace CloitreCollaboration.Certificate.Constants

open Primitive Operations WordArithmetic

theorem wordValue_zero_cons {A : Type} (f : A -> Int) (a : A) (w : List A) (ha : f a = 0) :
    wordValue f (a :: w) = wordValue f w := by
  unfold wordValue
  rw [List.reverse_cons, List.map_append, weighted_append]
  simp [weighted, ha]

theorem one_sink (w : List (Fin 2)) : run One 2 w = 2 := by
  have hs : forall c : Fin 2, One.step 2 c = 2 := by decide
  induction w with
  | nil => rfl
  | cons c w ih => simpa only [run, hs] using ih

theorem one_terminal (w : List (Fin 2)) (h : One.accept (run One 1 w) = true) : w = [] := by
  cases w with
  | nil => rfl
  | cons c w =>
      have hs : forall c : Fin 2, One.step 1 c = 2 := by decide
      rw [run, hs, one_sink] at h
      contradiction

theorem one_value (w : List (Fin 2)) (hw : accepts One w) : wordValue (digit 0) w = 1 := by
  induction w with
  | nil => contradiction
  | cons c w ih =>
      have hcases : c = 0 \/ c = 1 := by
        have : c.val = 0 \/ c.val = 1 := by omega
        simpa only [Fin.ext_iff, Fin.val_zero, Fin.val_one] using this
      rcases hcases with rfl | rfl
      · have ht : accepts One w := hw
        rw [wordValue_zero_cons _ _ _ (by decide)]
        exact ih ht
      · have ht : One.accept (run One 1 w) = true := hw
        obtain rfl := one_terminal w ht
        rfl

end CloitreCollaboration.Certificate.Constants
