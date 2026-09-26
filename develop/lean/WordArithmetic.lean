import RecurrenceBridge
import Mathlib.Data.List.Zip
import Mathlib.Data.List.TakeDrop

set_option autoImplicit false

namespace CloitreCollaboration.WordArithmetic

def wordValue {A : Type} (f : A -> Int) (w : List A) : Int :=
  weighted U 0 (w.reverse.map f)

def shiftValue {A : Type} (f : A -> Int) (w : List A) : Int :=
  weighted U 0 ((w.reverse.drop 2).map f)

theorem weighted_add {A : Type} (f g : A -> Int) (w : List A) (k : Nat) :
    weighted U k (w.map (fun a => f a + g a)) =
      weighted U k (w.map f) + weighted U k (w.map g) := by
  induction w generalizing k with
  | nil => simp [weighted]
  | cons a w ih => simp only [List.map_cons, weighted, ih]; ring

theorem weighted_sub {A : Type} (f g : A -> Int) (w : List A) (k : Nat) :
    weighted U k (w.map (fun a => f a - g a)) =
      weighted U k (w.map f) - weighted U k (w.map g) := by
  induction w generalizing k with
  | nil => simp [weighted]
  | cons a w ih => simp only [List.map_cons, weighted, ih]; ring

theorem wordValue_add {A : Type} (f g : A -> Int) (w : List A) :
    wordValue (fun a => f a + g a) w = wordValue f w + wordValue g w :=
  weighted_add f g w.reverse 0

theorem wordValue_sub {A : Type} (f g : A -> Int) (w : List A) :
    wordValue (fun a => f a - g a) w = wordValue f w - wordValue g w :=
  weighted_sub f g w.reverse 0

def linear (r : Carry) : Int := 2*r.a + 2*r.b + 3*r.c

theorem scan_value (digits : List Int) :
    weighted U 0 digits.reverse = linear (digits.foldl step zeroCarry) - digits.reverse.headD 0 := by
  rw [carry_value, reduce_reverse_eq_scan]
  rfl

theorem adder_scan_iff {A : Type} (x y z : A -> Int) (w : List A) :
    let digits := w.map (fun a => x a + y a - z a)
    linear (digits.foldl step zeroCarry) = digits.reverse.headD 0 <->
      wordValue x w + wordValue y w = wordValue z w := by
  dsimp only
  unfold linear
  rw [← scan_zero_iff]
  rw [← List.map_reverse]
  change wordValue (fun a => x a + y a - z a) w = 0 <-> _
  rw [wordValue_sub, wordValue_add]
  omega

theorem weighted_append (xs ys : List Int) (k : Nat) :
    weighted U k (xs ++ ys) = weighted U k xs + weighted U (k + xs.length) ys := by
  induction xs generalizing k with
  | nil => simp [weighted]
  | cons x xs ih =>
      simp only [List.cons_append, weighted, ih, List.length_cons]
      have hk : k + 1 + xs.length = k + (xs.length + 1) := by omega
      rw [hk]
      ring

def delayDigits (older recent : Int) : List Int -> List Int
  | [] => []
  | x :: xs => older :: delayDigits recent x xs

theorem delayDigits_take (xs : List Int) (older recent : Int) :
    delayDigits older recent xs = (older :: recent :: xs).take xs.length := by
  induction xs generalizing older recent with
  | nil => rfl
  | cons x xs ih => simp [delayDigits, ih]

theorem weighted_zeros (n k : Nat) : weighted U k ([0,0].drop n) = 0 := by
  rcases n with _ | _ | n <;> simp [weighted]

theorem delayed_value (xs : List Int) :
    weighted U 0 (delayDigits 0 0 xs).reverse = weighted U 0 (xs.reverse.drop 2) := by
  rw [delayDigits_take, List.reverse_take]
  simp only [List.length_cons]
  have hlen : xs.length + 1 + 1 - xs.length = 2 := by omega
  rw [hlen]
  simp only [List.reverse_cons, List.append_assoc]
  rw [List.drop_append, weighted_append]
  change weighted U 0 (xs.reverse.drop 2) +
    weighted U (0 + (xs.reverse.drop 2).length) ([0,0].drop (2 - xs.reverse.length)) = _
  rw [weighted_zeros]
  omega

def signedDigits {A : Type} (x y : A -> Int) (older recent : Int) : List A -> List Int
  | [] => []
  | a :: w => (older - y a) :: signedDigits x y recent (x a) w

theorem signed_length {A : Type} (x y : A -> Int) (w : List A) (u v : Int) :
    (signedDigits x y u v w).length = w.length := by
  induction w generalizing u v with
  | nil => rfl
  | cons a w ih => simp [signedDigits, ih]

theorem signed_eq_zip {A : Type} (x y : A -> Int) (w : List A) (u v : Int) :
    signedDigits x y u v w =
      List.zipWith (fun a b => a-b) (delayDigits u v (w.map x)) (w.map y) := by
  induction w generalizing u v with
  | nil => rfl
  | cons a w ih => simp [signedDigits, delayDigits, ih]

theorem weighted_zip_sub (xs ys : List Int) (k : Nat) (h : xs.length = ys.length) :
    weighted U k (List.zipWith (fun a b => a-b) xs ys) =
      weighted U k xs - weighted U k ys := by
  induction xs generalizing ys k with
  | nil =>
      have : ys = [] := by simpa using h.symm
      subst ys
      rfl
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zipWith_cons_cons, weighted]
          rw [ih ys (k+1) (by simpa using h)]
          ring

theorem signed_value {A : Type} (x y : A -> Int) (w : List A) :
    weighted U 0 (signedDigits x y 0 0 w).reverse = shiftValue x w - wordValue y w := by
  have hlen : (delayDigits 0 0 (w.map x)).length = (w.map y).length := by
    simp [delayDigits_take]
    omega
  rw [signed_eq_zip, List.reverse_zipWith hlen]
  rw [weighted_zip_sub _ _ _ (by simpa using hlen), delayed_value]
  simp [shiftValue, wordValue, List.map_reverse, List.map_drop]

structure DelayState where
  carry : Carry
  older : Int
  recent : Int
  last : Int
  deriving DecidableEq

def initial : DelayState := ⟨zeroCarry, 0, 0, 0⟩

def delayStep {A : Type} (x y : A -> Int) (s : DelayState) (a : A) : DelayState :=
  let z := s.older - y a
  ⟨step s.carry z, s.recent, x a, z⟩

def delayRun {A : Type} (x y : A -> Int) (s : DelayState) (w : List A) : DelayState :=
  w.foldl (delayStep x y) s

theorem delayRun_carry {A : Type} (x y : A -> Int) (w : List A) (s : DelayState) :
    (delayRun x y s w).carry = (signedDigits x y s.older s.recent w).foldl step s.carry := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
      change (delayRun x y (delayStep x y s a) w).carry = _
      rw [ih]
      rfl

theorem delayRun_last {A : Type} (x y : A -> Int) (w : List A) (s : DelayState) :
    (delayRun x y s w).last = (signedDigits x y s.older s.recent w).reverse.headD s.last := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
      change (delayRun x y (delayStep x y s a) w).last = _
      rw [ih]
      simp only [signedDigits, List.reverse_cons, delayStep]
      cases heq : (signedDigits x y s.recent (x a) w).reverse <;> simp

/-- Exact delay/carry invariant for arbitrary words and arbitrary integer input/output digits. -/
theorem delayRun_value {A : Type} (x y : A -> Int) (w : List A) :
    linear (delayRun x y initial w).carry - (delayRun x y initial w).last =
      shiftValue x w - wordValue y w := by
  rw [delayRun_carry, delayRun_last]
  change linear ((signedDigits x y 0 0 w).foldl step zeroCarry) -
    (signedDigits x y 0 0 w).reverse.headD 0 = _
  rw [← scan_value, signed_value]

theorem delayRun_sound {A : Type} (x y : A -> Int) (w : List A) (e : Int)
    (h : linear (delayRun x y initial w).carry - (delayRun x y initial w).last + e = 0) :
    wordValue y w = shiftValue x w + e := by
  rw [delayRun_value] at h
  omega

#print axioms adder_scan_iff
#print axioms delayRun_value
#print axioms delayRun_sound

end CloitreCollaboration.WordArithmetic
