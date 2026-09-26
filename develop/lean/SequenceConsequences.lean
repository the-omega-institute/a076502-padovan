import FinalIdentification
import GlobalConsequences
import IrrationalSlope

set_option autoImplicit false

namespace CloitreCollaboration.Certificate.Identification

theorem sequence_sharp_discrepancy (a : Nat → Nat) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (ha : NestedRecurrence a) (n : Nat) :
    -11/10 < (a n : ℝ)-Discrepancy.slope*n ∧
      (a n : ℝ)-Discrepancy.slope*n < 6/5 := by
  rw [sequence_identification a h0 h1 ha]
  have h := Candidate.error_bounds n
  unfold Candidate.error at h
  rw [← bNat_cast n] at h
  exact_mod_cast h

theorem sequence_exact_offsets (a : Nat → Nat) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (ha : NestedRecurrence a) :
    Set.range (fun n : Nat => (a n : Int)-⌊Discrepancy.slope*n⌋) =
      ({-1,0,1,2} : Set Int) := by
  ext z
  constructor
  · rintro ⟨n,rfl⟩
    simpa using sequence_offsets a h0 h1 ha n
  · intro hz
    rw [sequence_identification a h0 h1 ha]
    obtain ⟨h1,h2,h93,h1167⟩ := Candidate.offset_witnesses
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨1167,by simpa only [bNat_cast,Nat.cast_ofNat] using h1167⟩
    · exact ⟨2,by simpa only [bNat_cast,Nat.cast_ofNat] using h2⟩
    · exact ⟨1,by simpa only [bNat_cast,Nat.cast_one] using h1⟩
    · exact ⟨93,by simpa only [bNat_cast,Nat.cast_ofNat] using h93⟩

theorem sequence_four_balanced (a : Nat → Nat) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (ha : NestedRecurrence a) (i j len : Nat) :
    |((a (i+len) : Int)-a i)-((a (j+len) : Int)-a j)| ≤ 4 := by
  rw [sequence_identification a h0 h1 ha]
  simp only [bNat_cast]
  exact Candidate.four_balanced i j len

/-- No positive period can hold eventually for the signed first differences. -/
theorem sequence_not_eventually_periodic (a : Nat → Nat) (h0 : a 0 = 0)
    (h1 : a 1 = 1) (ha : NestedRecurrence a) :
    ¬ ∃ N p : Nat, 0 < p ∧ ∀ n, N ≤ n →
      (a (n+p+1) : Int)-a (n+p) = (a (n+1) : Int)-a n := by
  rintro ⟨N,p,hp,hper⟩
  let delta : Int := (a (N+p) : Int)-a N
  have hblock (k : Nat) : (a (N+k+p) : Int)-a (N+k) = delta := by
    induction k with
    | zero => simpa [delta]
    | succ k ih =>
      have hh := hper (N+k) (by omega)
      have he : N+(k+1)+p = N+k+p+1 := by omega
      have he' : N+(k+1) = N+k+1 := by omega
      rw [he,he']
      omega
  have hstride (k : Nat) : (a (N+k*p) : Int) = a N + k*delta := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := hblock (k*p)
      have he : N+(k+1)*p = N+k*p+p := by ring
      rw [he]
      push_cast
      nlinarith
  let t : ℝ := (delta : ℝ)-Discrepancy.slope*p
  have hbounded (k : Nat) : -3 < (k : ℝ)*t ∧ (k : ℝ)*t < 3 := by
    obtain ⟨hl,hu⟩ := sequence_sharp_discrepancy a h0 h1 ha (N+k*p)
    obtain ⟨hl0,hu0⟩ := sequence_sharp_discrepancy a h0 h1 ha N
    have hs : (a (N+k*p) : ℝ) = a N + (k : ℝ)*delta := by exact_mod_cast hstride k
    rw [hs] at hl hu
    push_cast at hl hu
    dsimp [t]
    constructor <;> nlinarith
  have ht : t = 0 := by
    rcases lt_trichotomy t 0 with hn | he | hp'
    · obtain ⟨k,hk⟩ := exists_nat_gt (3/(-t))
      have hm : 3 < (k : ℝ)*(-t) := (div_lt_iff₀ (by linarith)).mp hk
      nlinarith [(hbounded k).1]
    · exact he
    · obtain ⟨k,hk⟩ := exists_nat_gt (3/t)
      have hm : 3 < (k : ℝ)*t := (div_lt_iff₀ hp').mp hk
      linarith [(hbounded k).2]
  apply Discrepancy.slope_irrational
  refine ⟨(delta : ℚ)/p,?_⟩
  push_cast
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  apply (div_eq_iff hp').2
  dsimp [t] at ht
  linarith

#print axioms sequence_sharp_discrepancy
#print axioms sequence_exact_offsets
#print axioms sequence_four_balanced
#print axioms sequence_not_eventually_periodic

end CloitreCollaboration.Certificate.Identification
