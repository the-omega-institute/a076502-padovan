import GraphCandidate
import CompositionSemantics
import ConstantSemantics
import Generated.AdderTrace
import Generated.TotalRecurrence

set_option autoImplicit false

namespace CloitreCollaboration.Certificate.Identification

open Primitive Operations WordArithmetic

theorem b_zero : Candidate.b 0 = 0 := by
  have hb := Candidate.b_on_word 0 [] (by change (4 : Nat) < 6; decide) rfl
  exact hb

theorem b_one : Candidate.b 1 = 1 := by
  have hb := Candidate.b_on_word 1 [true] (by change (0 : Nat) < 6; decide) rfl
  exact hb

/-- The graph-defined candidate satisfies the literal recurrence at every integer input n>=2. -/
theorem candidate_integer_recurrence (n : Nat) (hn : 2 <= n) :
    bInt n = (n : Int) - bInt ((n : Int) - bInt ((n : Int) - bInt ((n : Int) - 1))) := by
  obtain ⟨w, hw, hv⟩ := Domains.every_nat_recurrence_domain n hn
  have hr := Composition.recurrence_value bInt graph_candidate adderValue Constants.one_value
    w (totalRecurrence w hw)
  change bInt (wordValue (digit 0) w) = _ at hr
  simpa only [Composition.val, hv] using hr

noncomputable def bNat (n : Nat) : Nat := (Candidate.b n).toNat

theorem bNat_cast (n : Nat) : (bNat n : Int) = Candidate.b n :=
  Int.toNat_of_nonneg (b_nonneg n)

theorem bNat_zero : bNat 0 = 0 := by simp [bNat, b_zero]

theorem bNat_one : bNat 1 = 1 := by simp [bNat, b_one]

theorem toNat_sub_b (n m : Nat) : ((n : Int) - Candidate.b m).toNat = n - bNat m := by
  rw [← bNat_cast m]
  exact Int.toNat_sub n (bNat m)

/-- Nonnegativity suffices to transport the integer identity to natural truncated subtraction. -/
theorem bNat_recurrence : NestedRecurrence bNat := by
  intro n hn
  have hr := congrArg Int.toNat (candidate_integer_recurrence n hn)
  have hpred : ((n : Int) - 1).toNat = n - 1 := by omega
  simp only [bInt, Int.toNat_natCast, hpred, toNat_sub_b] at hr
  exact hr

theorem bNat_bounds (n : Nat) (hn : 1 <= n) : 1 <= bNat n /\ bNat n <= n :=
  recurrence_bounds bNat bNat_one bNat_recurrence n hn

/-- Any sequence with the disclosed sentinel and literal A076502 recurrence is the candidate. -/
theorem sequence_identification (a : Nat -> Nat) (hzero : a 0 = 0) (hone : a 1 = 1)
    (ha : NestedRecurrence a) : a = bNat :=
  recurrence_unique_initial a bNat (hzero.trans bNat_zero.symm) hone bNat_one ha bNat_recurrence

theorem sequence_discrepancy (a : Nat -> Nat) (hzero : a 0 = 0) (hone : a 1 = 1)
    (ha : NestedRecurrence a) (n : Nat) :
    -2 < (a n : Real) - Discrepancy.slope * n /\
      (a n : Real) - Discrepancy.slope * n < 2 := by
  rw [sequence_identification a hzero hone ha]
  have h := candidate_discrepancy n
  rw [← bNat_cast n] at h
  exact_mod_cast h

theorem sequence_offsets (a : Nat -> Nat) (hzero : a 0 = 0) (hone : a 1 = 1)
    (ha : NestedRecurrence a) (n : Nat) :
    (a n : Int) - ⌊Discrepancy.slope * n⌋ ∈ ({-1,0,1,2} : Finset Int) := by
  rw [sequence_identification a hzero hone ha, bNat_cast]
  exact candidate_offsets n

theorem sequence_limit (a : Nat -> Nat) (hzero : a 0 = 0) (hone : a 1 = 1)
    (ha : NestedRecurrence a) :
    Filter.Tendsto (fun n : Nat => (a n : Real) / n) Filter.atTop (nhds Discrepancy.slope) := by
  rw [sequence_identification a hzero hone ha]
  have heq : (fun n : Nat => (bNat n : Real) / n) =
      (fun n : Nat => (Candidate.b n : Real) / n) := by
    funext n
    have hc : (bNat n : Real) = (Candidate.b n : Real) := by exact_mod_cast bNat_cast n
    rw [hc]
  rw [heq]
  exact candidate_limit

#print axioms bNat_recurrence
#print axioms sequence_identification
#print axioms sequence_discrepancy
#print axioms sequence_offsets
#print axioms sequence_limit

end CloitreCollaboration.Certificate.Identification
