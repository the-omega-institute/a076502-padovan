import TightSuffixCertificate
import PrefixCompression

set_option autoImplicit false

namespace CloitreCollaboration.TightSuffix

theorem scale_pos : (0 : ℝ) < scale := by norm_num [scale]

theorem slope_bracket : (lowerC : ℝ)/scale < Discrepancy.slope ∧
    Discrepancy.slope < (upperC : ℝ)/scale := by
  have hc : RootBrackets.polynomial Discrepancy.slope=0 := Discrepancy.slope_cubic
  constructor
  · apply RootBrackets.polynomial_strictMono.lt_iff_lt.mp
    rw [hc]
    norm_num [RootBrackets.polynomial,lowerC,scale]
  · apply RootBrackets.polynomial_strictMono.lt_iff_lt.mp
    rw [hc]
    norm_num [RootBrackets.polynomial,upperC,scale]

theorem weight_bracket (k : Fin 105) :
    (lowerWeight k : ℝ) ≤ (scale : ℝ)*Suffix.coefficient Discrepancy.slope k.val ∧
      (scale : ℝ)*Suffix.coefficient Discrepancy.slope k.val ≤ (upperWeight k : ℝ) := by
  obtain ⟨hw,hs⟩ := weight_data k
  obtain ⟨hl,hu⟩ := slope_bracket
  have hl' := (div_lt_iff₀ scale_pos).mp hl
  have hu' := (lt_div_iff₀ scale_pos).mp hu
  have hp : (0 : ℝ) ≤ weights k := by exact_mod_cast (weight_positive k).le
  have hshift : (shifted k : ℝ)=if 2 ≤ k.val then (U (k.val-2) : ℝ) else 0 := by
    rw [hs]
    split <;> simp_all
  unfold lowerWeight upperWeight Suffix.coefficient
  push_cast
  rw [←hshift,←hw]
  constructor
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ upperC-Discrepancy.slope*scale) hp]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Discrepancy.slope*scale-lowerC) hp]

theorem potential_sound {q last : Fin 28} {bs : List Bool}
    (hp : Suffix.Path q bs last) (hlen : bs.length ≤ 105) :
    (lowerPotential ⟨bs.length,by omega⟩ q : ℝ) ≤
      (scale : ℝ)*(Suffix.contribution Discrepancy.slope bs+(Suffix.output last : ℝ)) ∧
    (scale : ℝ)*(Suffix.contribution Discrepancy.slope bs+(Suffix.output last : ℝ)) ≤
      (upperPotential ⟨bs.length,by omega⟩ q : ℝ) := by
  induction hp with
  | nil q =>
    obtain ⟨h1,h2⟩ := base_certificate q
    simp only [List.length_nil,Suffix.contribution,zero_add]
    change (lowerPotential 0 q : ℝ) ≤ (scale : ℝ)*(Suffix.output q : ℝ) ∧
      (scale : ℝ)*(Suffix.output q : ℝ) ≤ (upperPotential 0 q : ℝ)
    rw [h1,h2]
    norm_num
  | @cons q q' last b bs he hp ih =>
    have hk : bs.length < 105 := by simp only [List.length_cons] at hlen; omega
    have hedge := edge_certificate ⟨bs.length,hk⟩ q q' b he
    have edge1 : (lowerPotential ⟨bs.length+1,by omega⟩ q : ℝ) ≤
      (if b then (lowerWeight ⟨bs.length,hk⟩ : ℝ) else 0)+
      (lowerPotential ⟨bs.length,by omega⟩ q' : ℝ) := by exact_mod_cast hedge.1
    have edge2 : (if b then (upperWeight ⟨bs.length,hk⟩ : ℝ) else 0)+
      (upperPotential ⟨bs.length,by omega⟩ q' : ℝ) ≤
      (upperPotential ⟨bs.length+1,by omega⟩ q : ℝ) := by exact_mod_cast hedge.2
    have hi := ih (by omega)
    have hb := weight_bracket ⟨bs.length,hk⟩
    simp only [List.length_cons,Suffix.contribution]
    cases b <;> simp only [Bool.false_eq_true,reduceIte] at *
    all_goals constructor <;> nlinarith [hi.1,hi.2,hb.1,hb.2]

theorem suffix_bound {q last : Fin 28} {bs : List Bool}
    (hp : Suffix.Path q bs last) (hlen : bs.length=105) :
    (lowerNumerator : ℝ)/scale ≤ Suffix.contribution Discrepancy.slope bs+(Suffix.output last : ℝ) ∧
    Suffix.contribution Discrepancy.slope bs+(Suffix.output last : ℝ) ≤ (upperNumerator : ℝ)/scale := by
  obtain ⟨h1,h2⟩ := potential_sound hp (by omega)
  have hf := final_certificate q
  have hf1 : (lowerNumerator : ℝ) ≤ lowerPotential 105 q := by exact_mod_cast hf.1
  have hf2 : (upperPotential 105 q : ℝ) ≤ upperNumerator := by exact_mod_cast hf.2
  have hh : (⟨bs.length,by omega⟩ : Fin 106)=105 := Fin.ext hlen
  rw [hh] at h1 h2
  constructor
  · apply (div_le_iff₀ scale_pos).2
    nlinarith
  · apply (le_div_iff₀ scale_pos).2
    nlinarith

theorem suffix_tail_bound (tail : ℝ) {q last : Fin 28} {bs : List Bool}
    (hp : Suffix.Path q bs last) (hlen : bs.length=105)
    (ht : |tail| ≤ Discrepancy.tailBound 102) :
    -1049234/1000000 < tail+Suffix.contribution Discrepancy.slope bs+(Suffix.output last : ℝ) ∧
      tail+Suffix.contribution Discrepancy.slope bs+(Suffix.output last : ℝ) < 1155081/1000000 := by
  obtain ⟨h1,h2⟩ := suffix_bound hp hlen
  obtain ⟨ht1,ht2⟩ := abs_le.mp ht
  norm_num [Discrepancy.tailBound,lowerNumerator,upperNumerator,scale] at h1 h2 ht1 ht2
  constructor <;> linarith

#print axioms suffix_tail_bound

end CloitreCollaboration.TightSuffix
