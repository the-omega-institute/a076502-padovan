import PrefixCompression
import ComputableSequence
import RationalRootBrackets
import WeightGrowth

set_option autoImplicit false

namespace CloitreCollaboration.EffectiveExtrema

open Candidate

def window (K : Nat) : Nat := (U (K+16)).toNat
def precision (K : Nat) : Nat := 4*K+64
def radius (K : Nat) : ℚ := 2*((5/16)*(7/8)^K)/(1-(7/8)^5)
def uncertainty (K : Nat) : ℚ :=
  (RootBrackets.hi (precision K)-RootBrackets.lo (precision K))*window K
def sample (K n : Nat) : ℚ :=
  (ComputableSequence.eval n : ℚ)-RootBrackets.hi (precision K)*n

theorem window_pos (K : Nat) : 0 < window K := by
  unfold window
  have := Greedy.U_pos (K+16)
  omega

def values (K : Nat) : Finset ℚ := (Finset.range (window K)).image (sample K)

theorem values_nonempty (K : Nat) : (values K).Nonempty := by
  exact ⟨sample K 0,Finset.mem_image.mpr ⟨0,Finset.mem_range.mpr (window_pos K),rfl⟩⟩

def minimum (K : Nat) : ℚ := (values K).min' (values_nonempty K)
def maximum (K : Nat) : ℚ := (values K).max' (values_nonempty K)
def infLower (K : Nat) : ℚ := minimum K-radius K
def infUpper (K : Nat) : ℚ := minimum K+uncertainty K
def supLower (K : Nat) : ℚ := maximum K
def supUpper (K : Nat) : ℚ := maximum K+uncertainty K+radius K

theorem radius_real (K : Nat) : (radius K : ℝ)=2*Discrepancy.tailBound K := by
  norm_num [radius,Discrepancy.tailBound]
  ring

theorem uncertainty_nonneg (K : Nat) : (0 : ℚ) ≤ uncertainty K := by
  rw [uncertainty,RootBrackets.width]
  positivity

theorem sample_error (K n : Nat) (hn : n < window K) :
    (sample K n : ℝ) ≤ error n ∧ error n ≤ (sample K n+uncertainty K : ℚ) := by
  obtain ⟨cl,cu⟩ := RootBrackets.bounds (precision K)
  have he : (ComputableSequence.eval n : ℝ)=(Candidate.b n : ℝ) := by
    exact_mod_cast ComputableSequence.eval_cast n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnB : (n : ℝ) ≤ window K := by exact_mod_cast hn.le
  have hc0 : (0 : ℝ) ≤ (RootBrackets.hi (precision K) : ℝ)-RootBrackets.lo (precision K) := by linarith
  simp only [sample,uncertainty,error]
  push_cast
  rw [he]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr cu) hn0]
  · nlinarith [mul_nonneg (sub_nonneg.mpr cl) hn0,
      mul_nonneg hc0 (sub_nonneg.mpr hnB)]

theorem min_le_sample (K n : Nat) (hn : n < window K) : minimum K ≤ sample K n :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr hn,rfl⟩)

theorem sample_le_max (K n : Nat) (hn : n < window K) : sample K n ≤ maximum K :=
  Finset.le_max' _ _ (Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr hn,rfl⟩)

theorem minimum_witness (K : Nat) : ∃ n < window K, sample K n=minimum K := by
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp (Finset.min'_mem (values K) (values_nonempty K))
  exact ⟨n,Finset.mem_range.mp hn,he⟩

theorem maximum_witness (K : Nat) : ∃ n < window K, sample K n=maximum K := by
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp (Finset.max'_mem (values K) (values_nonempty K))
  exact ⟨n,Finset.mem_range.mp hn,he⟩

theorem all_values_enclosed (K n : Nat) :
    (infLower K : ℝ) ≤ error n ∧ error n ≤ (supUpper K : ℝ) := by
  obtain ⟨m,hm,hclose⟩ := finite_window_approximation n (K+3) (by omega)
  have hm' : m < window K := by
    unfold window
    simp only [Nat.add_assoc,Nat.reduceAdd] at hm
    omega
  have hs := sample_error K m hm'
  have hlo : (minimum K : ℝ) ≤ sample K m := by exact_mod_cast min_le_sample K m hm'
  have hhi : (sample K m : ℝ) ≤ maximum K := by exact_mod_cast sample_le_max K m hm'
  obtain ⟨hcl,hcu⟩ := abs_le.mp hclose
  have hr := radius_real K
  simp only [Nat.add_sub_cancel] at hcl hcu
  unfold infLower supUpper
  push_cast at *
  constructor <;> linarith [hs.1,hs.2]

/-- Rational intervals computed by finite exhaustive search enclose the true global extrema. -/
theorem global_enclosures (K : Nat) :
    (infLower K : ℝ) ≤ globalInf ∧ globalInf ≤ (infUpper K : ℝ) ∧
      (supLower K : ℝ) ≤ globalSup ∧ globalSup ≤ (supUpper K : ℝ) := by
  obtain ⟨nlo,hnlo,helo⟩ := minimum_witness K
  obtain ⟨nhi,hnhi,hehi⟩ := maximum_witness K
  apply Discrepancy.global_extrema_enclosure error
    (infLower K) (supUpper K) (infUpper K) (supLower K)
    (fun n => (all_values_enclosed K n).1) (fun n => (all_values_enclosed K n).2) nlo nhi
  · have h := (sample_error K nlo hnlo).2
    rw [helo] at h
    exact h
  · have h := (sample_error K nhi hnhi).1
    rw [hehi] at h
    exact h

theorem interval_widths (K : Nat) :
    infUpper K-infLower K=uncertainty K+radius K ∧
      supUpper K-supLower K=uncertainty K+radius K := by
  constructor <;> simp only [infUpper,infLower,supUpper,supLower] <;> ring

theorem window_growth (K : Nat) : (window K : ℝ) ≤ (2 : ℝ)^(K+17) := by
  have hu := Greedy.U_exponential_bound (K+16)
  have hp := Greedy.U_pos (K+16)
  have hwi : (window K : Int)=U (K+16) := Int.toNat_of_nonneg hp.le
  have hb : (window K : Int) ≤ (2 : Int)^(K+17) := by
    rw [hwi]
    simpa only [Nat.add_assoc,Nat.reduceAdd] using hu.le
  exact_mod_cast hb

theorem uncertainty_bound (K : Nat) :
    (uncertainty K : ℝ) ≤ 131072*(1/8 : ℝ)^K := by
  have hw := window_growth K
  have hb : (1/2 : ℝ)^(precision K) ≤ (1/16 : ℝ)^K := by
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) ≤ 1) (show 4*K ≤ precision K by simp [precision])
    rw [pow_mul] at h
    norm_num at h
    exact h
  have he : (uncertainty K : ℝ)=(1/2 : ℝ)^(precision K)*(window K : ℝ) := by
    unfold uncertainty
    push_cast
    rw [← Rat.cast_sub,RootBrackets.width]
    push_cast
    rfl
  rw [he]
  calc
    _ ≤ (1/16 : ℝ)^K*(2 : ℝ)^(K+17) :=
      mul_le_mul hb hw (by positivity) (by positivity)
    _ = 131072*(1/8 : ℝ)^K := by
      rw [pow_add]
      rw [← mul_assoc,← mul_pow]
      norm_num
      ring

theorem widths_tendsto_zero :
    Filter.Tendsto (fun K => ((infUpper K-infLower K : ℚ) : ℝ)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun K => ((supUpper K-supLower K : ℚ) : ℝ)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun K => ((uncertainty K+radius K : ℚ) : ℝ)) Filter.atTop (nhds 0) := by
    apply Discrepancy.extrema_widths_tendsto _ 131072
    · intro K
      have hu : (0 : ℝ) ≤ uncertainty K := by exact_mod_cast uncertainty_nonneg K
      have hr : (0 : ℝ) ≤ radius K := by rw [radius_real]; unfold Discrepancy.tailBound; positivity
      push_cast
      linarith
    · intro K
      have hu := uncertainty_bound K
      push_cast
      rw [radius_real]
      linarith
  constructor
  · simpa only [(interval_widths _).1] using h
  · simpa only [(interval_widths _).2] using h

theorem interval_endpoints_tendsto (lower upper : Nat → ℝ) (x : ℝ)
    (hl : ∀ K, lower K ≤ x) (hu : ∀ K, x ≤ upper K)
    (hw : Filter.Tendsto (fun K => upper K-lower K) Filter.atTop (nhds 0)) :
    Filter.Tendsto lower Filter.atTop (nhds x) ∧
      Filter.Tendsto upper Filter.atTop (nhds x) := by
  have hgap1 : Filter.Tendsto (fun K => x-lower K) Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hw
    · intro K; exact sub_nonneg.mpr (hl K)
    · intro K; linarith [hl K,hu K]
  have hgap2 : Filter.Tendsto (fun K => upper K-x) Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hw
    · intro K; exact sub_nonneg.mpr (hu K)
    · intro K; linarith [hl K,hu K]
  constructor
  · have hc : Filter.Tendsto (fun _ : Nat => x) Filter.atTop (nhds x) := tendsto_const_nhds
    simpa only [sub_zero,sub_sub_cancel] using hc.sub hgap1
  · simpa only [zero_add,sub_add_cancel] using hgap2.add_const x

/-- Both computable rational endpoints converge to each true global extremum. -/
theorem endpoints_converge :
    Filter.Tendsto (fun K => (infLower K : ℝ)) Filter.atTop (nhds globalInf) ∧
    Filter.Tendsto (fun K => (infUpper K : ℝ)) Filter.atTop (nhds globalInf) ∧
    Filter.Tendsto (fun K => (supLower K : ℝ)) Filter.atTop (nhds globalSup) ∧
    Filter.Tendsto (fun K => (supUpper K : ℝ)) Filter.atTop (nhds globalSup) := by
  have hi := interval_endpoints_tendsto (fun K => (infLower K : ℝ))
    (fun K => (infUpper K : ℝ)) globalInf
    (fun K => (global_enclosures K).1) (fun K => (global_enclosures K).2.1)
    (by simpa only [Rat.cast_sub] using widths_tendsto_zero.1)
  have hs := interval_endpoints_tendsto (fun K => (supLower K : ℝ))
    (fun K => (supUpper K : ℝ)) globalSup
    (fun K => (global_enclosures K).2.2.1) (fun K => (global_enclosures K).2.2.2)
    (by simpa only [Rat.cast_sub] using widths_tendsto_zero.2)
  exact ⟨hi.1,hi.2,hs.1,hs.2⟩

#print axioms global_enclosures
#print axioms widths_tendsto_zero
#print axioms endpoints_converge

end CloitreCollaboration.EffectiveExtrema
