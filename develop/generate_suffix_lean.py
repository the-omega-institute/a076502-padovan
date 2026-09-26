"""Generate exact integer Bellman potentials; Lean checks their local inequalities."""
from pathlib import Path
import ast

root = Path(__file__).parent
tree = ast.parse((root.parent / 'correspondence/attachments/a076502_morphic_check.py').read_text())
table = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign)
             and any(isinstance(t, ast.Name) and t.id == 'E_DFAO' for t in n.targets))
Q = 10**12
CLO, CHI = 569840290998, 569840290999
weights = [1, 2, 3, 4, 5]
while len(weights) < 20:
    weights.append(weights[-2] + weights[-3])
low = [[Q*r[2] for r in table]]
high = [[Q*r[2] for r in table]]
for k in range(20):
    shifted = weights[k-2] if k >= 2 else 0
    low.append([min((b*(Q*shifted-CHI*weights[k])+low[-1][r[b]]
                     for b in (0, 1) if r[b] >= 0), default=10**30) for r in table])
    high.append([max((b*(Q*shifted-CLO*weights[k])+high[-1][r[b]]
                      for b in (0, 1) if r[b] >= 0), default=-10**30) for r in table])

def vec(xs):
    return '![' + ', '.join(str(x) for x in xs) + ']'

text = '''import Discrepancy

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace CloitreCollaboration.Suffix

def transitions : Fin 28 → Bool → Int :=
  fun q b => (TRANSITIONS q) (if b then 1 else 0)

def output : Fin 28 → Int := OUTPUT
def weights : Fin 20 → Int := WEIGHTS
def lowerPotential : Fin 21 → Fin 28 → Int := LOW
def upperPotential : Fin 21 → Fin 28 → Int := HIGH

def scale : Int := 1000000000000
def lowerC : Int := 569840290998
def upperC : Int := 569840290999
def shifted (k : Fin 20) : Int := if h : 2 ≤ k.val then weights ⟨k.val-2, by omega⟩ else 0
def lowerWeight (k : Fin 20) : Int := scale*shifted k-upperC*weights k
def upperWeight (k : Fin 20) : Int := scale*shifted k-lowerC*weights k

theorem base_certificate : ∀ q, lowerPotential 0 q=scale*output q ∧
    upperPotential 0 q=scale*output q := by decide

theorem edge_certificate : ∀ (k : Fin 20) (q q' : Fin 28) (b : Bool),
    transitions q b = q'.val →
    lowerPotential ⟨k.val+1, by omega⟩ q ≤
      (if b then lowerWeight k else 0)+lowerPotential ⟨k.val, by omega⟩ q' ∧
    (if b then upperWeight k else 0)+upperPotential ⟨k.val, by omega⟩ q' ≤
      upperPotential ⟨k.val+1, by omega⟩ q := by decide

theorem final_certificate : ∀ q, -1020207166563 ≤ lowerPotential 20 q ∧
    upperPotential 20 q ≤ 1132003467526 := by decide

end CloitreCollaboration.Suffix
'''
text = text.replace('TRANSITIONS',vec([vec(r[:2]) for r in table]))
text = text.replace('OUTPUT',vec([r[2] for r in table]))
text = text.replace('WEIGHTS',vec(weights))
text = text.replace('LOW',vec([vec(row) for row in low]))
text = text.replace('HIGH',vec([vec(row) for row in high]))
(root/'lean/SuffixCertificate.lean').write_text(text)
print('K20 extrema over all E states:',min(low[-1]),max(high[-1]))
