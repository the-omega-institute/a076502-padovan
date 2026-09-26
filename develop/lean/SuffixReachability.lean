import CandidateDiscrepancy

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CloitreCollaboration.Suffix

def checkedStep (q : Fin 28) (b : Bool) : Option (Fin 28) :=
  if h : 0 ≤ transitions q b ∧ transitions q b < 28 then
    some ⟨(transitions q b).toNat, by omega⟩ else none

def checkedRun (q : Fin 28) : List Bool → Option (Fin 28)
  | [] => some q
  | b::bs => (checkedStep q b).bind (fun q' => checkedRun q' bs)

theorem checkedStep_iff (q q' : Fin 28) (b : Bool) :
    checkedStep q b=some q' ↔ transitions q b=q'.val := by
  unfold checkedStep
  split
  · simp only [Option.some.injEq]
    constructor
    · intro h
      have hv : (transitions q b).toNat=q'.val := congrArg Fin.val h
      have hh : ((transitions q b).toNat : Int)=transitions q b := by omega
      omega
    · intro h
      apply Fin.ext
      simp [h]
  · rename_i hbad
    constructor
    · intro hnone
      cases hnone
    · intro he
      exfalso
      apply hbad
      rw [he]
      constructor <;> omega

theorem checkedRun_iff (q last : Fin 28) (bs : List Bool) :
    checkedRun q bs=some last ↔ Path q bs last := by
  induction bs generalizing q with
  | nil =>
    simp only [checkedRun,Option.some.injEq]
    constructor
    · rintro rfl; exact Path.nil q
    · intro h; cases h; rfl
  | cons b bs ih =>
    simp only [checkedRun,Option.bind_eq_some_iff]
    constructor
    · rintro ⟨q',he,hp⟩
      exact Path.cons ((checkedStep_iff q q' b).mp he) ((ih q').mp hp)
    · intro h
      cases h with
      | cons he hp => exact ⟨_,(checkedStep_iff _ _ _).mpr he,(ih _).mpr hp⟩

def reachingPrefix : Fin 28 → List Bool := ![[],
  [true], [true,false], [true,false,false], [true,false,false,false],
  [true,false,false,false,false], [true,false,false,false,true],
  [true,false,false,false,false,false], [true,false,false,false,false,true],
  [true,false,false,false,false,false,false], [true,false,false,false,false,false,true],
  [true,false,false,false,false,true,false], [true,false,false,false,false,false,false,true],
  [true,false,false,false,false,false,true,false], [true,false,false,false,false,true,false,false],
  [true,false,false,false,false,false,false,true,false], [true,false,false,false,false,false,true,false,false],
  [true,false,false,false,false,true,false,false,false],
  [true,false,false,false,false,false,false,true,false,false],
  [true,false,false,false,false,false,true,false,false,false],
  [true,false,false,false,false,true,false,false,false,false],
  [true,false,false,false,false,true,false,false,false,true],
  [true,false,false,false,false,false,false,true,false,false,false],
  [true,false,false,false,false,false,true,false,false,false,false],
  [true,false,false,false,false,true,false,false,false,false,false],
  [true,false,false,false,false,false,true,false,false,false,false,false],
  [true,false,false,false,false,true,false,false,false,false,false,false],
  [true,false,false,false,false,false,true,false,false,false,false,false,true]]

theorem reaching_certificate : ∀ q, checkedRun 0 (reachingPrefix q)=some q ∧
    (reachingPrefix q).length ≤ 13 := by decide

theorem reaching_path (q : Fin 28) : Path 0 (reachingPrefix q) q :=
  (checkedRun_iff _ _ _).mp (reaching_certificate q).1

def languageState : Fin 28 → Fin 7 :=
  ![4,0,1,2,3,4,5,4,0,4,0,1,0,1,2,1,2,3,2,3,4,5,3,4,4,4,4,0]

theorem language_certificate : (languageState 0=4) ∧
    (∀ q, languageState q ≠ 6) ∧
    (∀ (q q' : Fin 28) (b : Bool), transitions q b=q'.val →
      Greedy.dfaStep (languageState q) b=languageState q') := by decide

theorem path_language {q last : Fin 28} {bs : List Bool} (hp : Path q bs last) :
    Greedy.dfaRun (languageState q) bs=languageState last := by
  induction hp with
  | nil q => rfl
  | cons he hp ih =>
    change Greedy.dfaRun (Greedy.dfaStep _ _) _=_
    rw [language_certificate.2.2 _ _ _ he]
    exact ih

theorem initial_path_legal {last : Fin 28} {bs : List Bool} (hp : Path 0 bs last) :
    Greedy.AcceptsFrom 4 bs := by
  unfold Greedy.AcceptsFrom
  have hl := path_language hp
  rw [language_certificate.1] at hl
  rw [hl]
  have := language_certificate.2.1 last
  have := (languageState last).isLt
  omega

theorem path_concat {q mid last : Fin 28} {pref suf : List Bool}
    (h1 : Path q pref mid) (h2 : Path mid suf last) : Path q (pref++suf) last := by
  induction h1 with
  | nil => exact h2
  | cons he hp ih => exact Path.cons he (ih h2)

/-- Every legal suffix from every E state has a concrete realizing prefix of length ≤13. -/
theorem suffix_realizable {q last : Fin 28} {bs : List Bool} (hp : Path q bs last) :
    Path 0 (reachingPrefix q++bs) last ∧
    Greedy.AcceptsFrom 4 (reachingPrefix q++bs) ∧ (reachingPrefix q).length ≤ 13 := by
  have hp' := path_concat (reaching_path q) hp
  exact ⟨hp',initial_path_legal hp',(reaching_certificate q).2⟩

#print axioms suffix_realizable

end CloitreCollaboration.Suffix
