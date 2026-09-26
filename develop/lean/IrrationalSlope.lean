import RationalRootBrackets
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.ComputeDegree

set_option autoImplicit false

namespace CloitreCollaboration.Discrepancy

theorem slope_irrational : Irrational slope := by
  rintro ⟨q,hq⟩
  let p : Polynomial Int := Polynomial.X^3-Polynomial.X^2+Polynomial.C 2*Polynomial.X-Polynomial.C 1
  have hp : p.Monic := by dsimp [p]; monicity!
  have hqr : q^3-q^2+2*q-1 = 0 := by
    have hc := slope_cubic
    rw [← hq] at hc
    exact_mod_cast hc
  have hroot : Polynomial.aeval q p = 0 := by
    simp only [p,map_sub,map_add,map_pow,map_mul,Polynomial.aeval_X,Polynomial.aeval_C]
    norm_num
    exact hqr
  obtain ⟨z,hz,_⟩ := exists_integer_of_is_root_of_monic hp hroot
  have hreal : (z : ℝ) = slope := by
    have hcast : (z : ℚ) = q := hz.symm
    exact (show (z : ℝ) = (q : ℝ) by exact_mod_cast hcast).trans hq
  obtain ⟨hl,hu⟩ := Candidate.slope_bracket
  have hz0 : (0 : Int) < z := by exact_mod_cast (show (0 : ℝ) < z by rw [hreal]; linarith)
  have hz1 : z < (1 : Int) := by exact_mod_cast (show (z : ℝ) < 1 by rw [hreal]; linarith)
  omega

#print axioms slope_irrational

end CloitreCollaboration.Discrepancy
