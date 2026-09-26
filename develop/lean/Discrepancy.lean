import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic
import RecurrenceBridge

set_option autoImplicit false

namespace CloitreCollaboration.Discrepancy

noncomputable section

def energy (r x y : ℝ) : ℝ := r⁻¹*x^2+r*x*y+y^2

theorem energy_contract (r x y : ℝ) (hr : r ≠ 0) (_hc : r^3=r+1) :
    energy r y (-r*y-r⁻¹*x) = r⁻¹*energy r x y := by
  unfold energy
  field_simp
  ring

theorem energy_square (r x y : ℝ) (hr : r ≠ 0) :
    energy r x y = (y+r*x/2)^2+(4-r^3)/(4*r)*x^2 := by
  unfold energy
  field_simp
  ring

theorem energy_lower (r x y : ℝ) (hpos : 0 < r) (hc : r^3=r+1)
    (hupper : r < 4/3) : (5/16)*x^2 ≤ energy r x y := by
  rw [energy_square r x y (ne_of_gt hpos)]
  have hk : (5/16 : ℝ) ≤ (4-r^3)/(4*r) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*r)).2
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hk (sq_nonneg x), sq_nonneg (y+r*x/2)]

theorem energy_iterate (r : ℝ) (hr : r ≠ 0) (hc : r^3=r+1)
    (d : ℕ → ℝ) (hd : ∀ n, d (n+2) = -r*d (n+1)-r⁻¹*d n) (n : ℕ) :
    energy r (d n) (d (n+1)) = (r⁻¹)^n*energy r (d 0) (d 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n+1+1=n+2 by omega, hd n, energy_contract r _ _ hr hc, ih, pow_succ]
    ring

def realU (n : ℕ) : ℝ := (U n : ℝ)

theorem realU_recurrence (n : ℕ) : realU (n+4)=realU (n+2)+realU (n+1) := by
  unfold realU
  exact_mod_cast U_recurrence n

def delta (r : ℝ) (n : ℕ) : ℝ := realU (n+1)-(r⁻¹)^2*realU (n+3)

def spectral (r : ℝ) (n : ℕ) : ℝ :=
  realU (n+3)+r*realU (n+2)+r⁻¹*realU (n+1)

theorem spectral_step (r : ℝ) (hr : r ≠ 0) (hc : r^3=r+1) (n : ℕ) :
    spectral r (n+1)=r*spectral r n := by
  have he : r^2=1+r⁻¹ := by field_simp; nlinarith
  unfold spectral
  rw [show n+1+3=n+4 by omega, show n+1+2=n+3 by omega,
    show n+1+1=n+2 by omega, realU_recurrence]
  field_simp at he ⊢
  linear_combination -realU (n+2)*hc

theorem delta_recurrence (r : ℝ) (hr : r ≠ 0) (hc : r^3=r+1) (n : ℕ) :
    delta r (n+2) = -r*delta r (n+1)-r⁻¹*delta r n := by
  have h1 := spectral_step r hr hc n
  have h2 := spectral_step r hr hc (n+1)
  have hs : spectral r n-(r⁻¹)^2*spectral r (n+2)=0 := by
    rw [show n+2=n+1+1 by omega, h2, h1]
    field_simp
    ring
  unfold delta spectral at *
  simp only [Nat.add_assoc] at *
  linear_combination hs

theorem rho_bounds (r : ℝ) (hr : 1 < r) (hc : r^3=r+1) :
    331/250 < r ∧ r < 53/40 := by
  constructor
  · by_contra h
    have hh : r ≤ 331/250 := le_of_not_gt h
    have hp : 0 ≤ r^2+r*(331/250)+(331/250)^2-1 := by nlinarith
    have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hh) hp
    nlinarith
  · by_contra h
    have hh : 53/40 ≤ r := le_of_not_gt h
    have hp : 0 ≤ r^2+r*(53/40)+(53/40)^2-1 := by nlinarith
    have hm := mul_nonneg (sub_nonneg.mpr hh) hp
    nlinarith

theorem inverse_square_bounds (r : ℝ) (hr : 1 < r) (hc : r^3=r+1) :
    1600/2809 < (r⁻¹)^2 ∧ (r⁻¹)^2 < 62500/109561 := by
  obtain ⟨hl, hu⟩ := rho_bounds r hr hc
  have hr0 : 0 < r := by linarith
  rw [inv_pow]
  constructor
  · apply (lt_inv_comm₀ (by norm_num) (by positivity)).2
    norm_num
    nlinarith [sq_nonneg (r-53/40)]
  · apply (inv_lt_comm₀ (by positivity) (by norm_num)).2
    norm_num
    nlinarith [sq_nonneg (r-331/250)]

theorem initial_energy_bound (r : ℝ) (hr : 1 < r) (hc : r^3=r+1) :
    energy r (delta r 0) (delta r 1) < 3/100 := by
  obtain ⟨hrl, hru⟩ := rho_bounds r hr hc
  obtain ⟨cl, cu⟩ := inverse_square_bounds r hr hc
  rw [inv_pow] at cl cu
  have hi : r⁻¹ < 19/25 := by
    apply (inv_lt_comm₀ (by linarith) (by norm_num)).2
    norm_num
    linarith
  have hx : -141/500 < delta r 0 ∧ delta r 0 < -139/500 := by
    norm_num [delta, realU, U, W]
    constructor <;> nlinarith
  have hy : 147/1000 < delta r 1 ∧ delta r 1 < 153/1000 := by
    norm_num [delta, realU, U, W]
    constructor <;> nlinarith
  have hx2 : (delta r 0)^2 < (141/500)^2 := by nlinarith [hx.1, hx.2]
  have hy2 : (delta r 1)^2 < (153/1000)^2 := by nlinarith [hy.1, hy.2]
  have hxy : delta r 0*delta r 1 < -(139/500)*(147/1000) := by
    nlinarith [mul_pos (by linarith [hx.2] : 0 < -139/500-delta r 0)
      (by linarith [hy.1] : 0 < delta r 1-147/1000)]
  have hterm := mul_lt_mul_of_pos_left hxy (by linarith : 0 < r)
  have hfirst : r⁻¹*(delta r 0)^2 < (19/25)*(141/500)^2 := by
    calc
      _ ≤ (19/25)*(delta r 0)^2 := mul_le_mul_of_nonneg_right hi.le (sq_nonneg _)
      _ < _ := mul_lt_mul_of_pos_left hx2 (by norm_num)
  unfold energy
  nlinarith

theorem delta_decay (r : ℝ) (hr : 1 < r) (hc : r^3=r+1) (n : ℕ) :
    |delta r n| < (5/16)*(7/8)^n := by
  have hp : 0 < r := by linarith
  have hn : r ≠ 0 := ne_of_gt hp
  obtain ⟨hl, hu⟩ := rho_bounds r hr hc
  have hinv : r⁻¹ ≤ (49/64 : ℝ) := by
    apply (inv_le_comm₀ hp (by norm_num)).2
    norm_num
    linarith
  have ep := energy_iterate r hn hc (delta r) (delta_recurrence r hn hc) n
  have el := energy_lower r (delta r n) (delta r (n+1)) hp hc (by linarith)
  have e0 := initial_energy_bound r hr hc
  have hb : energy r (delta r n) (delta r (n+1)) < (3/100)*(49/64)^n := by
    rw [ep]
    calc
      _ < (r⁻¹)^n*(3/100) := mul_lt_mul_of_pos_left e0 (by positivity)
      _ ≤ (49/64)^n*(3/100) := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hinv n) (by norm_num)
      _ = _ := by ring
  have hs : (delta r n)^2 < ((5/16)*(7/8)^n)^2 := by
    have heq : ((7/8 : ℝ)^n)^2=(49/64 : ℝ)^n := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    have hpositive : 0 < (49/64 : ℝ)^n := by positivity
    rw [mul_pow, heq]
    nlinarith
  have hnonneg : 0 ≤ (5/16 : ℝ)*(7/8)^n := by positivity
  exact (sq_lt_sq₀ (abs_nonneg _) hnonneg).mp (by simpa only [sq_abs] using hs)

open scoped BigOperators

theorem finite_geometric_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, q^i ≤ 1/(1-q) := by
  rw [geom_sum_eq (ne_of_lt hq1)]
  have hd : q-1 < 0 := by linarith
  apply (div_le_iff_of_neg hd).2
  have he : 1/(1-q)*(q-1)=(-1 : ℝ) := by
    field_simp [ne_of_gt (sub_pos.mpr hq1)]
    ring
  rw [he]
  nlinarith [pow_nonneg hq0 n]

theorem sparse_tail_bound (r : ℝ) (hr : 1 < r) (hc : r^3=r+1)
    (positions : ℕ → ℕ) (K N : ℕ) (hs : ∀ j < N, K+5*j ≤ positions j) :
    |∑ j ∈ Finset.range N, delta r (positions j)| ≤
      ((5/16)*(7/8)^K)/(1-(7/8)^5) := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, |delta r (positions j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, (5/16 : ℝ)*(7/8)^(K+5*j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hd := (delta_decay r hr hc (positions j)).le
      exact hd.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (hs j (Finset.mem_range.mp hj))) (by norm_num))
    _ = ((5/16 : ℝ)*(7/8)^K)*∑ j ∈ Finset.range N, ((7/8 : ℝ)^5)^j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add, pow_mul]
      ring
    _ ≤ ((5/16 : ℝ)*(7/8)^K)*(1/(1-(7/8)^5)) := by
      apply mul_le_mul_of_nonneg_left
      · exact finite_geometric_bound _ (by norm_num) (by norm_num) N
      · positivity
    _ = _ := by ring

open Filter Topology

theorem bounded_discrepancy_limit (a : ℕ → ℝ) (c B : ℝ)
    (hb : ∀ n, |a n-c*n| ≤ B) :
    Tendsto (fun n : ℕ => a n/n) atTop (𝓝 c) := by
  have hd : Tendsto (fun n : ℕ => (a n-c*n)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero
      (Eventually.of_forall fun n => (abs_le.mp (hb n)).1)
      (Eventually.of_forall fun n => (abs_le.mp (hb n)).2)
      tendsto_natCast_atTop_atTop
  have ht := hd.add_const c
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp
  ring

def tailBound (K : ℕ) : ℝ := ((5/16)*(7/8)^K)/(1-(7/8)^5)

theorem tailBound_tendsto : Tendsto tailBound atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 7/8) (by norm_num : (7/8 : ℝ) < 1)).const_mul (5/16)
  change Tendsto (fun K : ℕ => ((5/16 : ℝ)*(7/8)^K)/(1-(7/8)^5)) atTop (𝓝 0)
  simpa using h.div_const (1-(7/8 : ℝ)^5)

/-- If independently certified extrema intervals have a geometric error budget,
their widths converge to zero. Both rates are explicit and strictly below one. -/
theorem extrema_widths_tendsto (width : ℕ → ℝ) (C : ℝ)
    (h0 : ∀ K, 0 ≤ width K)
    (hb : ∀ K, width K ≤ 2*tailBound K+C*(1/8)^K) :
    Tendsto width atTop (𝓝 0) := by
  have h1 := tailBound_tendsto.const_mul 2
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/8) (by norm_num : (1/8 : ℝ) < 1)).const_mul C
  have hsum := h1.add h2
  simp only [mul_zero, add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum h0 hb

theorem coefficient_cubic (r : ℝ) (hr : r ≠ 0) (hc : r^3=r+1) :
    ((r⁻¹)^2)^3-((r⁻¹)^2)^2+2*(r⁻¹)^2-1=0 := by
  field_simp
  linear_combination -(r^3-r+1)*hc

theorem exists_plastic_root : ∃ r : ℝ, 1 < r ∧ r^3=r+1 := by
  have hf : ContinuousOn (fun x : ℝ => x^3-x-1) (Set.Icc 1 2) := by fun_prop
  have hm : (0 : ℝ) ∈ Set.Icc ((1 : ℝ)^3-1-1) ((2 : ℝ)^3-2-1) := by norm_num
  obtain ⟨r,hr,hroot⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hf hm
  refine ⟨r,?_,?_⟩
  · by_contra h
    have he : r=1 := le_antisymm (le_of_not_gt h) hr.1
    norm_num [he] at hroot
  · nlinarith

theorem plastic_root_unique (r s : ℝ) (hr : 1 < r) (hs : 1 < s)
    (hcr : r^3=r+1) (hcs : s^3=s+1) : r=s := by
  have hf : 0 < r^2+r*s+s^2-1 := by nlinarith [sq_nonneg (r-s)]
  have he : (r-s)*(r^2+r*s+s^2-1)=0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (ne_of_gt hf))

def rho : ℝ := Classical.choose exists_plastic_root
theorem rho_gt_one : 1 < rho := (Classical.choose_spec exists_plastic_root).1
theorem rho_cubic : rho^3=rho+1 := (Classical.choose_spec exists_plastic_root).2
def slope : ℝ := (rho⁻¹)^2

theorem slope_cubic : slope^3-slope^2+2*slope-1=0 :=
  coefficient_cubic rho (by linarith [rho_gt_one]) rho_cubic

theorem coefficient_bracket (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hc : c^3-c^2+2*c-1=0) :
    569840290998/1000000000000 < c ∧ c < 569840290999/1000000000000 := by
  constructor
  · by_contra h
    have hh : c ≤ 569840290998/1000000000000 := le_of_not_gt h
    have hp : 0 ≤ c^2+c*(569840290998/1000000000000)+
        (569840290998/1000000000000)^2-c-569840290998/1000000000000+2 := by
      nlinarith [sq_nonneg c]
    have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hh) hp
    nlinarith
  · by_contra h
    have hh : 569840290999/1000000000000 ≤ c := le_of_not_gt h
    have hp : 0 ≤ c^2+c*(569840290999/1000000000000)+
        (569840290999/1000000000000)^2-c-569840290999/1000000000000+2 := by
      nlinarith [sq_nonneg c]
    have hm := mul_nonneg (sub_nonneg.mpr hh) hp
    nlinarith

theorem floor_offsets (a : ℤ) (x : ℝ) (hl : -2 < (a : ℝ)-x)
    (hu : (a : ℝ)-x < 2) : a-⌊x⌋ ∈ ({-1,0,1,2} : Finset ℤ) := by
  have hf := Int.floor_le x
  have hg := Int.lt_floor_add_one x
  have hlow : (-2 : ℤ) < a-⌊x⌋ := by
    exact_mod_cast (show (-2 : ℝ) < (a : ℝ)-(⌊x⌋ : ℝ) by linarith)
  have hhigh : a-⌊x⌋ < (3 : ℤ) := by
    exact_mod_cast (show (a : ℝ)-(⌊x⌋ : ℝ) < (3 : ℝ) by linarith)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem global_extrema_enclosure (f : ℕ → ℝ) (L H u l : ℝ)
    (hL : ∀ n, L ≤ f n) (hH : ∀ n, f n ≤ H)
    (nmin nmax : ℕ) (hmin : f nmin ≤ u) (hmax : l ≤ f nmax) :
    L ≤ sInf (Set.range f) ∧ sInf (Set.range f) ≤ u ∧
      l ≤ sSup (Set.range f) ∧ sSup (Set.range f) ≤ H := by
  have hne : (Set.range f).Nonempty := ⟨f 0, ⟨0, rfl⟩⟩
  have hbbelow : BddBelow (Set.range f) := ⟨L, by rintro _ ⟨n, rfl⟩; exact hL n⟩
  have hbabove : BddAbove (Set.range f) := ⟨H, by rintro _ ⟨n, rfl⟩; exact hH n⟩
  refine ⟨le_csInf hne ?_, (csInf_le hbbelow ⟨nmin, rfl⟩).trans hmin,
    hmax.trans (le_csSup hbabove ⟨nmax, rfl⟩), csSup_le hne ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact hL n
  · rintro _ ⟨n, rfl⟩
    exact hH n

#print axioms delta_recurrence
#print axioms rho_bounds
#print axioms delta_decay
#print axioms sparse_tail_bound
#print axioms bounded_discrepancy_limit
#print axioms extrema_widths_tendsto
#print axioms floor_offsets
#print axioms global_extrema_enclosure

end

end CloitreCollaboration.Discrepancy
