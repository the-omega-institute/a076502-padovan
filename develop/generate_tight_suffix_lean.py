"""Generate a K=105 Bellman certificate; every edge is kernel-checked in Lean."""
from fractions import Fraction as F
from pathlib import Path
import ast

root = Path(__file__).parent
tree = ast.parse((root.parent / 'correspondence/attachments/a076502_morphic_check.py').read_text())
table = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign)
             and any(isinstance(t, ast.Name) and t.id == 'E_DFAO' for t in n.targets))
low_c, high_c = F(0), F(1)
for _ in range(160):
    mid = (low_c+high_c)/2
    if mid**3-mid**2+2*mid-1 <= 0:
        low_c = mid
    else:
        high_c = mid
Q = 2**160
CLO, CHI = int(low_c*Q), int(high_c*Q)
N = 105
weights = [1, 2, 3, 4, 5]
while len(weights) < N:
    weights.append(weights[-2]+weights[-3])
low = [[Q*r[2] for r in table]]
high = [[Q*r[2] for r in table]]
for k in range(N):
    shifted = weights[k-2] if k >= 2 else 0
    low.append([min((b*(Q*shifted-CHI*weights[k])+low[-1][r[b]]
                     for b in (0, 1) if r[b] >= 0), default=10**100) for r in table])
    high.append([max((b*(Q*shifted-CLO*weights[k])+high[-1][r[b]]
                      for b in (0, 1) if r[b] >= 0), default=-10**100) for r in table])

def lookup(values):
    if len(values) == 1:
        return f'(.leaf ({values[0]}))'
    return f'(.node {lookup(values[::2])} {lookup(values[1::2])})'

text = '''import SuffixSoundness
import RationalRootBrackets
import AutomataCertificate

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CloitreCollaboration.TightSuffix

open Certificate

def scale : Int := SCALE
def lowerC : Int := CLO
def upperC : Int := CHI
def lowerNumerator : Int := LBOUND
def upperNumerator : Int := HBOUND
def weightTable : Lookup Int := WEIGHTS
def lowerTable : Lookup Int := LOW
def upperTable : Lookup Int := HIGH
def weights (k : Fin 105) : Int := weightTable.get k.val
def lowerPotential (k : Fin 106) (q : Fin 28) : Int := lowerTable.get (k.val*28+q.val)
def upperPotential (k : Fin 106) (q : Fin 28) : Int := upperTable.get (k.val*28+q.val)
def shifted (k : Fin 105) : Int := if h : 2 ≤ k.val then weights ⟨k.val-2, by omega⟩ else 0
def lowerWeight (k : Fin 105) : Int := scale*shifted k-upperC*weights k
def upperWeight (k : Fin 105) : Int := scale*shifted k-lowerC*weights k

theorem base_certificate : ∀ q, lowerPotential 0 q=scale*Suffix.output q ∧
    upperPotential 0 q=scale*Suffix.output q := by decide

theorem compact_edge_certificate : ∀ (k : Fin 105) (q : Fin 28) (b : Bool),
    0 ≤ Suffix.transitions q b →
    let q' := Fin.ofNat 28 (Suffix.transitions q b).toNat
    lowerPotential ⟨k.val+1, by omega⟩ q ≤
      (if b then lowerWeight k else 0)+lowerPotential ⟨k.val, by omega⟩ q' ∧
    (if b then upperWeight k else 0)+upperPotential ⟨k.val, by omega⟩ q' ≤
      upperPotential ⟨k.val+1, by omega⟩ q := by decide

theorem edge_certificate (k : Fin 105) (q q' : Fin 28) (b : Bool)
    (he : Suffix.transitions q b=q'.val) :
    lowerPotential ⟨k.val+1, by omega⟩ q ≤
      (if b then lowerWeight k else 0)+lowerPotential ⟨k.val, by omega⟩ q' ∧
    (if b then upperWeight k else 0)+upperPotential ⟨k.val, by omega⟩ q' ≤
      upperPotential ⟨k.val+1, by omega⟩ q := by
  have h := compact_edge_certificate k q b (by rw [he]; omega)
  simpa only [he,Int.toNat_natCast,Fin.ofNat_eq_cast,Fin.cast_val_eq_self] using h

theorem final_certificate : ∀ q, lowerNumerator ≤ lowerPotential 105 q ∧
    upperPotential 105 q ≤ upperNumerator := by decide

theorem weight_recurrence : ∀ k : Fin 101,
    weights ⟨k.val+4,by omega⟩=weights ⟨k.val+2,by omega⟩+weights ⟨k.val+1,by omega⟩ := by decide

theorem weights_eq_U (n : Nat) (hn : n < 105) : weights ⟨n,hn⟩=U n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | n
    · change weights 0=1; decide
    · change weights 1=2; decide
    · change weights 2=3; decide
    · change weights 3=4; decide
    · have hw := weight_recurrence ⟨n,by omega⟩
      rw [U_recurrence]
      rw [hw,ih (n+2) (by omega) (by omega),ih (n+1) (by omega) (by omega)]

theorem weight_data (k : Fin 105) : weights k = U k.val ∧
    shifted k = if 2 ≤ k.val then U (k.val-2) else 0 := by
  constructor
  · exact weights_eq_U k.val k.isLt
  · unfold shifted
    split
    · exact weights_eq_U _ _
    · rfl

theorem weight_positive : ∀ k : Fin 105, 0 < weights k := by decide

end CloitreCollaboration.TightSuffix
'''
for key, value in dict(SCALE=Q,CLO=CLO,CHI=CHI,LBOUND=min(low[-1]),HBOUND=max(high[-1]),
                       WEIGHTS=lookup(weights),LOW=lookup(sum(low,[])),HIGH=lookup(sum(high,[]))).items():
    text = text.replace(key,str(value))
(root/'lean/TightSuffixCertificate.lean').write_text(text)
print('scale',Q)
print('coefficients',CLO,CHI)
print('suffix bounds',F(min(low[-1]),Q),F(max(high[-1]),Q))
