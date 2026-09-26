import SuffixCertificate

set_option autoImplicit false

namespace CloitreCollaboration.Suffix

noncomputable section

inductive Path : Fin 28 → List Bool → Fin 28 → Prop
  | nil (q) : Path q [] q
  | cons {q q' last : Fin 28} {b : Bool} {bs : List Bool} :
      transitions q b = q'.val → Path q' bs last → Path q (b::bs) last

def coefficient (c : ℝ) (p : ℕ) : ℝ :=
  (if 2 ≤ p then (U (p-2) : ℝ) else 0)-c*(U p : ℝ)

def contribution (c : ℝ) : List Bool → ℝ
  | [] => 0
  | b::bs => (if b then coefficient c bs.length else 0)+contribution c bs

theorem weight_data : ∀ k : Fin 20, weights k = U k.val ∧
    shifted k = if 2 ≤ k.val then U (k.val-2) else 0 := by decide

theorem weight_positive : ∀ k : Fin 20, 0 < weights k := by decide

theorem weight_bracket (c : ℝ)
    (hl : 569840290998/1000000000000 ≤ c)
    (hu : c ≤ 569840290999/1000000000000) (k : Fin 20) :
    (lowerWeight k : ℝ) ≤ 1000000000000*coefficient c k.val ∧
      1000000000000*coefficient c k.val ≤ (upperWeight k : ℝ) := by
  obtain ⟨hw, hs⟩ := weight_data k
  have hp : 0 ≤ (weights k : ℝ) := by exact_mod_cast (weight_positive k).le
  have hshift : (shifted k : ℝ) = if 2 ≤ k.val then (U (k.val-2) : ℝ) else 0 := by
    rw [hs]
    split <;> simp_all
  unfold lowerWeight upperWeight coefficient
  push_cast
  rw [← hshift, ← hw]
  norm_num [scale, lowerC, upperC]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu) hp]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hl) hp]

theorem potential_sound (c : ℝ)
    (hl : 569840290998/1000000000000 ≤ c)
    (hu : c ≤ 569840290999/1000000000000)
    {q last : Fin 28} {bs : List Bool} (hpath : Path q bs last) (hlen : bs.length ≤ 20) :
    (lowerPotential ⟨bs.length, by omega⟩ q : ℝ) ≤
      1000000000000*(contribution c bs+(output last : ℝ)) ∧
    1000000000000*(contribution c bs+(output last : ℝ)) ≤
      (upperPotential ⟨bs.length, by omega⟩ q : ℝ) := by
  induction hpath with
  | nil q =>
    obtain ⟨h1,h2⟩ := base_certificate q
    simp only [List.length_nil, contribution, zero_add]
    change (lowerPotential 0 q : ℝ) ≤ 1000000000000*(output q : ℝ) ∧
      1000000000000*(output q : ℝ) ≤ (upperPotential 0 q : ℝ)
    rw [h1,h2]
    norm_num [scale]
  | @cons q q' last b bs he hp ih =>
    have hk : bs.length < 20 := by simp only [List.length_cons] at hlen; omega
    have edge := edge_certificate ⟨bs.length,hk⟩ q q' b he
    have edge1 : (lowerPotential ⟨bs.length+1, by omega⟩ q : ℝ) ≤
        (if b then (lowerWeight ⟨bs.length,hk⟩ : ℝ) else 0)+
          (lowerPotential ⟨bs.length,by omega⟩ q' : ℝ) := by exact_mod_cast edge.1
    have edge2 : (if b then (upperWeight ⟨bs.length,hk⟩ : ℝ) else 0)+
        (upperPotential ⟨bs.length,by omega⟩ q' : ℝ) ≤
          (upperPotential ⟨bs.length+1,by omega⟩ q : ℝ) := by exact_mod_cast edge.2
    have ih' := ih (by omega)
    have hb := weight_bracket c hl hu ⟨bs.length,hk⟩
    simp only [List.length_cons, contribution]
    cases b <;> simp only [Bool.false_eq_true, reduceIte] at *
    all_goals constructor <;> linarith [ih'.1,ih'.2,hb.1,hb.2]

theorem suffix20_bound (c : ℝ)
    (hl : 569840290998/1000000000000 ≤ c)
    (hu : c ≤ 569840290999/1000000000000)
    {q last : Fin 28} {bs : List Bool} (hpath : Path q bs last) (hlen : bs.length=20) :
    -1020207166563/1000000000000 ≤ contribution c bs+(output last : ℝ) ∧
      contribution c bs+(output last : ℝ) ≤ 1132003467526/1000000000000 := by
  obtain ⟨h1,h2⟩ := potential_sound c hl hu hpath (by omega)
  have hf := final_certificate q
  have hf1 : (-1020207166563 : ℝ) ≤ (lowerPotential 20 q : ℝ) := by exact_mod_cast hf.1
  have hf2 : (upperPotential 20 q : ℝ) ≤ (1132003467526 : ℝ) := by exact_mod_cast hf.2
  have hh : (⟨bs.length, by omega⟩ : Fin 21)=20 := Fin.ext hlen
  rw [hh] at h1 h2
  constructor <;> linarith

theorem initial_zero_loop : transitions 0 false=0 := by decide

theorem path_leading_zeros {bs : List Bool} {last : Fin 28}
    (hp : Path 0 bs last) (n : ℕ) : Path 0 (List.replicate n false++bs) last := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
    simpa only [List.replicate_succ, List.cons_append] using Path.cons initial_zero_loop ih

theorem contribution_leading_zero (c : ℝ) (bs : List Bool) :
    contribution c (false::bs)=contribution c bs := by simp [contribution]

theorem suffix_tail_offset (c tail : ℝ) {q last : Fin 28} {bs : List Bool}
    (hl : 569840290998/1000000000000 ≤ c)
    (hu : c ≤ 569840290999/1000000000000)
    (hp : Path q bs last) (hlen : bs.length=20)
    (ht : |tail| ≤ Discrepancy.tailBound 17) :
    -2 < tail+contribution c bs+(output last : ℝ) ∧
      tail+contribution c bs+(output last : ℝ) < 2 := by
  obtain ⟨h1,h2⟩ := suffix20_bound c hl hu hp hlen
  obtain ⟨ht1,ht2⟩ := abs_le.mp ht
  norm_num [Discrepancy.tailBound] at ht1 ht2
  constructor <;> linarith

theorem suffix_tail_sharp (c tail : ℝ) {q last : Fin 28} {bs : List Bool}
    (hl : 569840290998/1000000000000 ≤ c)
    (hu : c ≤ 569840290999/1000000000000)
    (hp : Path q bs last) (hlen : bs.length=20)
    (ht : |tail| ≤ Discrepancy.tailBound 17) :
    -11/10 < tail+contribution c bs+(output last : ℝ) ∧
      tail+contribution c bs+(output last : ℝ) < 6/5 := by
  obtain ⟨h1,h2⟩ := suffix20_bound c hl hu hp hlen
  obtain ⟨ht1,ht2⟩ := abs_le.mp ht
  norm_num [Discrepancy.tailBound] at ht1 ht2
  constructor <;> linarith

#print axioms potential_sound
#print axioms suffix20_bound
#print axioms suffix_tail_offset

end

end CloitreCollaboration.Suffix
