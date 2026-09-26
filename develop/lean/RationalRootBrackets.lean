import OffsetWitnesses

set_option autoImplicit false

namespace CloitreCollaboration.RootBrackets

def cubic (q : ℚ) : ℚ := q^3-q^2+2*q-1

def polynomial (x : ℝ) : ℝ := x^3-x^2+2*x-1

theorem polynomial_strictMono : StrictMono polynomial := by
  intro x y hxy
  have hp : 0 < y^2+x*y+x^2-y-x+2 := by
    nlinarith [sq_nonneg (x-y),sq_nonneg (x+y-2/3)]
  have hm := mul_pos (sub_pos.mpr hxy) hp
  have he : polynomial y-polynomial x = (y-x)*(y^2+x*y+x^2-y-x+2) := by
    unfold polynomial
    ring
  rw [← he] at hm
  linarith

theorem cubic_cast (q : ℚ) : (cubic q : ℝ) = polynomial q := by
  unfold cubic polynomial
  push_cast
  rfl

theorem cubic_sign (q : ℚ) : cubic q ≤ 0 ↔ (q : ℝ) ≤ Discrepancy.slope := by
  have hr : polynomial Discrepancy.slope = 0 := Discrepancy.slope_cubic
  have hcast : cubic q ≤ 0 ↔ (cubic q : ℝ) ≤ 0 := by exact_mod_cast Iff.rfl
  rw [hcast,cubic_cast,← hr]
  exact polynomial_strictMono.le_iff_le

def bracket : Nat → ℚ × ℚ
  | 0 => (0,1)
  | n+1 =>
      let b := bracket n
      let m := (b.1+b.2)/2
      if cubic m ≤ 0 then (m,b.2) else (b.1,m)

def lo (n : Nat) : ℚ := (bracket n).1
def hi (n : Nat) : ℚ := (bracket n).2

theorem bounds (n : Nat) : (lo n : ℝ) ≤ Discrepancy.slope ∧
    Discrepancy.slope ≤ (hi n : ℝ) := by
  change ((bracket n).1 : ℝ) ≤ Discrepancy.slope ∧
    Discrepancy.slope ≤ ((bracket n).2 : ℝ)
  induction n with
  | zero =>
    obtain ⟨hl,hu⟩ := Candidate.slope_bracket
    norm_num only [bracket, Rat.cast_zero, Rat.cast_one]
    constructor <;> linarith
  | succ n ih =>
    simp only [bracket]
    split_ifs with h
    · exact ⟨(cubic_sign _).mp h,ih.2⟩
    · exact ⟨ih.1,(lt_of_not_ge (mt (cubic_sign _).mpr h)).le⟩

theorem width (n : Nat) : hi n-lo n = (1/2 : ℚ)^n := by
  change (bracket n).2-(bracket n).1 = (1/2 : ℚ)^n
  induction n with
  | zero => norm_num [bracket]
  | succ n ih =>
    simp only [bracket]
    split_ifs <;> dsimp
    all_goals rw [pow_succ,← ih]; ring

theorem ordered (n : Nat) : lo n ≤ hi n := by
  have h := width n
  have hp : (0 : ℚ) ≤ (1/2)^n := pow_nonneg (by norm_num) n
  linarith

theorem width_real (n : Nat) : (hi n : ℝ)-(lo n : ℝ) = (1/2 : ℝ)^n := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (width n)
  push_cast at h
  exact h

#print axioms bounds
#print axioms width

end CloitreCollaboration.RootBrackets
