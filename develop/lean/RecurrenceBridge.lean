import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace CloitreCollaboration

/-- The literal A076502 recurrence, with the two initial inputs kept separate. -/
def NestedRecurrence (f : Nat -> Nat) : Prop :=
  forall n, 2 <= n -> f n = n - f (n - f (n - f (n - 1)))

/-- The literal recurrence and first value already force positive index bounds. -/
theorem recurrence_bounds (a : Nat -> Nat) (hone : a 1 = 1)
    (ha : NestedRecurrence a) :
    forall n, 1 <= n -> 1 <= a n /\ a n <= n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      rcases n with _ | _ | k
      · omega
      · simp [hone]
      · have hp : k + 2 - 1 = k + 1 := by omega
        have hpred := ih (k + 1) (by omega) (by omega)
        have hi2pos : 1 <= k + 2 - a (k + 1) := by omega
        have hi2lt : k + 2 - a (k + 1) < k + 2 := by omega
        have hinner := ih (k + 2 - a (k + 1)) hi2lt hi2pos
        have hi3pos : 1 <= k + 2 - a (k + 2 - a (k + 1)) := by omega
        have hi3lt : k + 2 - a (k + 2 - a (k + 1)) < k + 2 := by omega
        have houter := ih (k + 2 - a (k + 2 - a (k + 1))) hi3lt hi3pos
        rw [ha (k + 2) (by omega), hp]
        omega

/-- A candidate satisfying the literal recurrence is uniquely determined.
Only the reference function needs bounds; the candidate inherits them. -/
theorem recurrence_unique (a b : Nat -> Nat)
    (hzero : a 0 = b 0) (hone : a 1 = b 1)
    (ha : NestedRecurrence a) (hb : NestedRecurrence b)
    (bounds : forall n, 1 <= n -> 1 <= a n /\ a n <= n) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | k
      · exact hzero
      · exact hone
      · have hp : k + 2 - 1 = k + 1 := by omega
        have hpred := ih (k + 1) (by omega)
        have hpredBounds := bounds (k + 1) (by omega)
        have hi2pos : 1 <= k + 2 - a (k + 1) := by omega
        have hi2lt : k + 2 - a (k + 1) < k + 2 := by omega
        have hinner := ih (k + 2 - a (k + 1)) hi2lt
        have hinnerBounds := bounds (k + 2 - a (k + 1)) hi2pos
        have hi3lt : k + 2 - a (k + 2 - a (k + 1)) < k + 2 := by omega
        have houter := ih (k + 2 - a (k + 2 - a (k + 1))) hi3lt
        rw [ha (k + 2) (by omega), hb (k + 2) (by omega), hp]
        rw [houter, hinner, hpred]

/-- A candidate identification needs only the initial values and literal recurrence.
No separate global bounds premise or access to private reference lemmas is needed. -/
theorem recurrence_unique_initial (a b : Nat -> Nat)
    (hzero : a 0 = b 0) (haone : a 1 = 1) (hbone : b 1 = 1)
    (ha : NestedRecurrence a) (hb : NestedRecurrence b) : a = b := by
  exact recurrence_unique a b hzero (haone.trans hbone.symm) ha hb
    (recurrence_bounds a haone ha)

/-- The homogeneous weight sequence used by reduction modulo X^3-X-1. -/
def W : Nat -> Int
  | 0 => 2
  | 1 => 2
  | 2 => 3
  | n + 3 => W (n + 1) + W n

/-- Cloitre's positional weights. Only the weight at zero is anomalous. -/
def U : Nat -> Int
  | 0 => 1
  | n + 1 => W (n + 1)

theorem U_initial : (U 0, U 1, U 2, U 3, U 4) = (1, 2, 3, 4, 5) := by
  decide

theorem U_recurrence (n : Nat) : U (n + 4) = U (n + 2) + U (n + 1) := by
  change W ((n + 1) + 3) = W ((n + 1) + 1) + W (n + 1)
  rw [W]

structure Carry where
  a : Int
  b : Int
  c : Int
  deriving DecidableEq

def zeroCarry : Carry := ⟨0, 0, 0⟩

/-- Horner multiplication by X, then insertion of one integer digit. -/
def step (r : Carry) (z : Int) : Carry := ⟨r.c + z, r.a + r.c, r.b⟩

def evalAt (k : Nat) (r : Carry) : Int :=
  r.a * W k + r.b * W (k + 1) + r.c * W (k + 2)

theorem evalAt_step (k : Nat) (r : Carry) (z : Int) :
    evalAt k (step r z) = evalAt (k + 1) r + z * W k := by
  simp only [evalAt, step]
  have hw : W (k + 1 + 2) = W (k + 1) + W k := by
    change W (k + 3) = W (k + 1) + W k
    rw [W]
  rw [hw]
  have hk : k + 1 + 1 = k + 2 := by omega
  rw [hk]
  ring

/-- Digits are listed least significant first; reduction processes the tail first. -/
def reduce : List Int -> Carry
  | [] => zeroCarry
  | z :: zs => step (reduce zs) z

theorem reduce_eq_foldr (digits : List Int) :
    reduce digits = digits.foldr (fun z r => step r z) zeroCarry := by
  induction digits with
  | nil => rfl
  | cons z zs ih => simp only [reduce, List.foldr_cons, ih]

/-- The same reduction is a left-to-right Horner scan of most-significant-first digits. -/
theorem reduce_reverse_eq_scan (digits : List Int) :
    reduce digits.reverse = digits.foldl step zeroCarry := by
  rw [reduce_eq_foldr, List.foldr_reverse]

def weighted (weights : Nat -> Int) (k : Nat) : List Int -> Int
  | [] => 0
  | z :: zs => z * weights k + weighted weights (k + 1) zs

theorem reduce_invariant (digits : List Int) (k : Nat) :
    evalAt k (reduce digits) = weighted W k digits := by
  induction digits generalizing k with
  | nil => simp [reduce, evalAt, zeroCarry, weighted]
  | cons z zs ih =>
      simp only [reduce, evalAt_step, weighted, ih]
      ring

theorem weights_agree_above_zero (digits : List Int) (k : Nat) (hk : 1 <= k) :
    weighted U k digits = weighted W k digits := by
  induction digits generalizing k with
  | nil => rfl
  | cons z zs ih =>
      obtain ⟨j, rfl⟩ : exists j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [weighted, U]
      rw [ih (j + 1 + 1) (by omega)]

/-- Exact terminal carry condition, including the exceptional least-significant weight.
This is valid for arbitrary integer digits, hence also signed addition digits. -/
theorem carry_value (digits : List Int) :
    weighted U 0 digits =
      2 * (reduce digits).a + 2 * (reduce digits).b + 3 * (reduce digits).c -
        digits.headD 0 := by
  have hinv := reduce_invariant digits 0
  simp only [evalAt, W] at hinv
  cases digits with
  | nil => simp [weighted, reduce, zeroCarry]
  | cons z zs =>
      simp only [weighted, List.headD_cons, U] at *
      rw [weights_agree_above_zero zs 1 (by omega)]
      change (reduce (z :: zs)).a * 2 + (reduce (z :: zs)).b * 2 +
        (reduce (z :: zs)).c * 3 = z * 2 + weighted W 1 zs at hinv
      omega

theorem carry_zero_iff (digits : List Int) :
    weighted U 0 digits = 0 <->
      2 * (reduce digits).a + 2 * (reduce digits).b + 3 * (reduce digits).c =
        digits.headD 0 := by
  rw [carry_value]
  omega

/-- Sound and complete terminal equality for an unbounded Horner carry scan.
No finite-state truncation, greedy-language hypothesis, or candidate recurrence
identity is assumed or proved by this statement. -/
theorem scan_zero_iff (digits : List Int) :
    weighted U 0 digits.reverse = 0 <->
      let r := digits.foldl step zeroCarry
      2 * r.a + 2 * r.b + 3 * r.c = digits.reverse.headD 0 := by
  rw [carry_zero_iff, reduce_reverse_eq_scan]

#print axioms recurrence_bounds
#print axioms recurrence_unique
#print axioms recurrence_unique_initial
#print axioms U_recurrence
#print axioms reduce_invariant
#print axioms carry_value
#print axioms carry_zero_iff
#print axioms scan_zero_iff

end CloitreCollaboration
