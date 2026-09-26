import GreedyRepresentation
import Discrepancy

set_option autoImplicit false

namespace CloitreCollaboration.Greedy

open Discrepancy

theorem admissible_append_left (ps qs : List Nat) (h : Admissible (ps ++ qs)) :
    Admissible ps := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
      cases ps with
      | nil => trivial
      | cons q ps => exact ⟨h.1, ih h.2⟩

theorem high_positions_admissible (pref suf : List Bool)
    (h : BinaryAdmissible (pref ++ suf).reverse) :
    Admissible (positions suf.length pref.reverse) := by
  unfold BinaryAdmissible at h
  rw [List.reverse_append, positions_append] at h
  simp only [List.length_reverse, Nat.zero_add] at h
  exact admissible_append_left _ _ h

theorem high_positions_lower (pref suf : List Bool) (p : Nat)
    (hp : p ∈ positions suf.length pref.reverse) : suf.length <= p :=
  positions_lower _ _ _ hp

noncomputable def tailSum (r : Real) (ps : List Nat) : Real :=
  (ps.map (fun p => delta r (p - 3))).sum

theorem ascending_tail_bound (r : Real) (hr : 1 < r) (hc : r^3 = r+1)
    (ps : List Nat) (hsp : List.Pairwise (fun p q => p + 5 <= q) ps)
    (K : Nat) (hlo : forall p, p ∈ ps -> K + 3 <= p) :
    |tailSum r ps| <= tailBound K := by
  induction ps generalizing K with
  | nil => simp [tailSum, tailBound]; positivity
  | cons p ps ih =>
      have hp := hlo p (List.mem_cons_self)
      have hs := List.pairwise_cons.mp hsp
      have ht := ih hs.2 (K + 5) (by
        intro q hq
        have := hs.1 q hq
        omega)
      have hd : |delta r (p - 3)| <= (5/16 : Real) * (7/8)^K := by
        apply (delta_decay r hr hc (p - 3)).le.trans
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have heq : (5/16 : Real) * (7/8)^K + tailBound (K + 5) = tailBound K := by
        unfold tailBound
        rw [pow_add]
        field_simp
        ring
      calc
        |tailSum r (p :: ps)| = |delta r (p - 3) + tailSum r ps| := rfl
        _ <= |delta r (p - 3)| + |tailSum r ps| := abs_add_le _ _
        _ <= (5/16 : Real) * (7/8)^K + tailBound (K + 5) := add_le_add hd ht
        _ = tailBound K := heq

/-- Every admissible high-position list satisfies the geometric tail estimate. -/
theorem admissible_tail_bound (r : Real) (hr : 1 < r) (hc : r^3 = r+1)
    (ps : List Nat) (ha : Admissible ps) (K : Nat)
    (hlo : forall p, p ∈ ps -> K + 3 <= p) :
    |tailSum r ps| <= tailBound K := by
  have hpair := admissible_pairwise ps ha
  have hdesc : List.Pairwise (fun p q => q + 5 <= p) ps := by
    apply hpair.imp_of_mem
    intro p q hp hq hgap
    have := hlo q hq
    rcases hgap with hgap | hgap
    · exact hgap
    · omega
  have hasc : List.Pairwise (fun p q => p + 5 <= q) ps.reverse := by
    simpa only [List.pairwise_reverse] using hdesc
  have hb := ascending_tail_bound r hr hc ps.reverse hasc K (by
    intro p hp
    exact hlo p (List.mem_reverse.mp hp))
  simpa [tailSum, List.map_reverse] using hb

#print axioms admissible_tail_bound

end CloitreCollaboration.Greedy
