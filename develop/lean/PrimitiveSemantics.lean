import AutomataCertificate
import WordArithmetic
import GreedyRepresentation
import SuffixSoundness

set_option autoImplicit false

namespace CloitreCollaboration.Certificate.Primitive

open WordArithmetic

def digit {k : Nat} (i : Nat) (a : Fin k) : Int := (a.val / 2^i % 2 : Nat)

def bit {k : Nat} (i : Nat) (a : Fin k) : Bool := a.val / 2^i % 2 == 1

def greedyMachine : Machine 2 7 where
  start := 4
  step q a := Greedy.dfaStep q (bit 0 a)
  accept q := q != 6

def addStep (s : Carry × Int) (a : Fin 8) : Carry × Int :=
  let z := digit 2 a + digit 1 a - digit 0 a
  (CloitreCollaboration.step s.1 z, z)

def addGood (s : Carry × Int) : Bool := decide (linear s.1 = s.2)

def eStep (q : Fin 28) (b : Bool) : Fin 28 :=
  Fin.ofNat 28 (Suffix.transitions q b).toNat

def eRun (q : Fin 28) (w : List Bool) : Fin 28 := w.foldl eStep q

def graphStep (s : DelayState × Fin 28) (a : Fin 4) : DelayState × Fin 28 :=
  (delayStep (digit 1) (digit 0) s.1 a, eStep s.2 (bit 1 a))

def graphGood (s : DelayState × Fin 28) : Bool :=
  decide (linear s.1.carry - s.1.last + Suffix.output s.2 = 0)

theorem graph_fold (w : List (Fin 4)) (s : DelayState × Fin 28) :
    w.foldl graphStep s = (delayRun (digit 1) (digit 0) s.1 w,
      eRun s.2 (w.map (bit 1))) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => simpa only [List.foldl_cons, List.map_cons, graphStep,
      delayRun, eRun] using ih (graphStep s a)

theorem graph_trace_value (w : List (Fin 4))
    (h : graphGood (w.foldl graphStep (initial, 0)) = true) :
    wordValue (digit 0) w = shiftValue (digit 1) w +
      Suffix.output (eRun 0 (w.map (bit 1))) := by
  rw [graph_fold] at h
  apply delayRun_sound
  simpa only [graphGood, decide_eq_true_eq] using h

theorem add_fold (w : List (Fin 8)) (s : Carry × Int) :
    (w.foldl addStep s).1 =
      (w.map (fun a => digit 2 a + digit 1 a - digit 0 a)).foldl CloitreCollaboration.step s.1 ∧
    (w.foldl addStep s).2 =
      (w.map (fun a => digit 2 a + digit 1 a - digit 0 a)).reverse.headD s.2 := by
  induction w generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons a w ih =>
    obtain ⟨h1,h2⟩ := ih (addStep s a)
    constructor
    · exact h1
    · simp only [List.foldl_cons, List.map_cons, List.reverse_cons]
      rw [h2]
      cases (w.map (fun a => digit 2 a + digit 1 a - digit 0 a)).reverse <;>
        simp [addStep]

theorem add_trace_value (w : List (Fin 8))
    (h : addGood (w.foldl addStep (zeroCarry,0)) = true) :
    wordValue (digit 2) w + wordValue (digit 1) w = wordValue (digit 0) w := by
  obtain ⟨h1,h2⟩ := add_fold w (zeroCarry,0)
  simp only [addGood, decide_eq_true_eq, h1, h2] at h
  exact (adder_scan_iff (digit 2) (digit 1) (digit 0) w).mp h

def PathCheck {k n : Nat} (m : Machine k n) (input : Fin k → Bool)
    (label : Fin n → Option (Fin 28)) : Prop :=
  label m.start = some 0 ∧
  (∀ q c, (label (m.step q c)).isSome = true →
    (label q).any (fun s => (label (m.step q c)).any
      (fun t => decide (Suffix.transitions s (input c) = t.val))) = true) ∧
  (∀ q, m.accept q = true → (label q).isSome = true)

instance {k n : Nat} (m : Machine k n) (input : Fin k → Bool)
    (label : Fin n → Option (Fin 28)) : Decidable (PathCheck m input label) := by
  unfold PathCheck
  infer_instance

theorem path_sound {k n : Nat} (m : Machine k n) (input : Fin k → Bool)
    (label : Fin n → Option (Fin 28)) (h : PathCheck m input label)
    (w : List (Fin k)) (hw : accepts m w) : ∃ last, Suffix.Path 0 (w.map input) last := by
  have lift : ∀ w q s, label (run m q w) = some s →
      ∃ t, label q = some t ∧ Suffix.Path t (w.map input) s := by
    intro v
    induction v with
    | nil => intro q s hs; exact ⟨s,hs,Suffix.Path.nil s⟩
    | cons c v ih =>
      intro q s hs
      obtain ⟨t,ht,hp⟩ := ih (m.step q c) s hs
      have he := h.2.1 q c (by simp [ht])
      cases hq : label q with
      | none => simp [hq] at he
      | some r =>
        have hedge : Suffix.transitions r (input c) = t.val := by simpa [hq,ht] using he
        exact ⟨r,rfl,Suffix.Path.cons hedge hp⟩
  have hf := h.2.2 _ hw
  cases hs : label (run m m.start w) with
  | none => simp [hs] at hf
  | some s =>
    obtain ⟨t,ht,hp⟩ := lift w m.start s hs
    have heq : t = 0 := by simpa [h.1] using ht.symm
    subst t
    exact ⟨s,hp⟩

theorem eRun_of_path {q last : Fin 28} {w : List Bool} (h : Suffix.Path q w last) :
    eRun q w = last := by
  induction h with
  | nil q => rfl
  | @cons q q' last b bs he hp ih =>
    have hstep : eStep q b = q' := by
      unfold eStep
      rw [he]
      simp
    simpa only [eRun, List.foldl_cons, hstep] using ih

end CloitreCollaboration.Certificate.Primitive
