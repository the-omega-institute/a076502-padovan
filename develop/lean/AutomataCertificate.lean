import Mathlib.Computability.DFA
import Mathlib.Data.List.Forall2

set_option autoImplicit false

namespace CloitreCollaboration.Certificate

inductive Lookup (α : Type) where
  | leaf : α → Lookup α
  | node : Lookup α → Lookup α → Lookup α

def Lookup.get {α : Type} : Lookup α → Nat → α
  | .leaf a, _ => a
  | .node l r, n => if n % 2 = 0 then l.get (n / 2) else r.get (n / 2)

/-- A finite, total transition table. Partial automata use an explicit sink. -/
structure Machine (alphabet states : Nat) where
  start : Fin states
  step : Fin states → Fin alphabet → Fin states
  accept : Fin states → Bool

def run {k n : Nat} (m : Machine k n) (q : Fin n) : List (Fin k) → Fin n
  | [] => q
  | a :: w => run m (m.step q a) w

def accepts {k n : Nat} (m : Machine k n) (w : List (Fin k)) : Prop :=
  m.accept (run m m.start w) = true

/-- A supplied relation is a proof certificate, not an assumed language inclusion. -/
theorem inclusion_of_invariant {k n p : Nat} (a : Machine k n) (b : Machine k p)
    (r : Fin n → Fin p → Prop)
    (initial : r a.start b.start)
    (closed : ∀ q s c, r q s → r (a.step q c) (b.step s c))
    (final : ∀ q s, r q s → a.accept q = true → b.accept s = true) :
    ∀ w, accepts a w → accepts b w := by
  have invariant : ∀ w q s, r q s → r (run a q w) (run b s w) := by
    intro w
    induction w with
    | nil => intro q s h; exact h
    | cons c w ih =>
      intro q s h
      exact ih _ _ (closed q s c h)
  intro w ha
  exact final _ _ (invariant w _ _ initial) ha

def relation {n p : Nat} (pairs : List (Fin n × Fin p)) (q : Fin n) (s : Fin p) : Prop :=
  (q, s) ∈ pairs

/-- Only a finite set of local conditions is checked, but the result quantifies
over every word length. All checks are ordinary kernel-reduced propositions. -/
def Valid {k n p : Nat} (a : Machine k n) (b : Machine k p)
    (pairs : List (Fin n × Fin p)) : Prop :=
  (a.start, b.start) ∈ pairs ∧
  ∀ qs ∈ pairs,
    (a.accept qs.1 = true → b.accept qs.2 = true) ∧
    ∀ c : Fin k, (a.step qs.1 c, b.step qs.2 c) ∈ pairs

instance {k n p : Nat} (a : Machine k n) (b : Machine k p)
    (pairs : List (Fin n × Fin p)) : Decidable (Valid a b pairs) := by
  unfold Valid
  letI := List.decidableBAll (fun qs : Fin n × Fin p =>
    (a.accept qs.1 = true → b.accept qs.2 = true) ∧
    ∀ c : Fin k, (a.step qs.1 c, b.step qs.2 c) ∈ pairs) pairs
  exact instDecidableAnd

theorem valid_implies_inclusion {k n p : Nat} (a : Machine k n) (b : Machine k p)
    (pairs : List (Fin n × Fin p)) (h : Valid a b pairs) :
    ∀ w, accepts a w → accepts b w := by
  apply inclusion_of_invariant a b (relation pairs) h.1
  · intro q s c hrs
    exact (h.2 (q,s) hrs).2 c
  · intro q s hrs
    exact (h.2 (q,s) hrs).1

/-- Indexed closure witnesses avoid repeatedly searching a long state-pair list. -/
def CoverValid {k n p r : Nat} (a : Machine k n) (b : Machine k p)
    (nodes : Fin r → Fin n × Fin p) (first : Fin r)
    (edges : Fin r → Fin k → Fin r) : Prop :=
  nodes first = (a.start,b.start) ∧
  ∀ i, (a.accept (nodes i).1 = true → b.accept (nodes i).2 = true) ∧
    ∀ c, nodes (edges i c) = (a.step (nodes i).1 c, b.step (nodes i).2 c)

instance {k n p r : Nat} (a : Machine k n) (b : Machine k p)
    (nodes : Fin r → Fin n × Fin p) (first : Fin r)
    (edges : Fin r → Fin k → Fin r) : Decidable (CoverValid a b nodes first edges) := by
  unfold CoverValid
  infer_instance

theorem cover_inclusion {k n p r : Nat} (a : Machine k n) (b : Machine k p)
    (nodes : Fin r → Fin n × Fin p) (first : Fin r)
    (edges : Fin r → Fin k → Fin r) (h : CoverValid a b nodes first edges) :
    ∀ w, accepts a w → accepts b w := by
  apply inclusion_of_invariant a b (fun q s => ∃ i, nodes i = (q,s)) ⟨first,h.1⟩
  · intro q s c hi
    obtain ⟨i,hi⟩ := hi
    exact ⟨edges i c, by simpa [hi] using (h.2 i).2 c⟩
  · intro q s hi hq
    obtain ⟨i,hi⟩ := hi
    simpa [hi] using (h.2 i).1 (by simpa [hi] using hq)

/-- A commuting map preserves arbitrary-length runs. This checks minimization
or state renaming by its concrete map, rather than trusting the minimizer. -/
theorem run_map {k n p : Nat} (a : Machine k n) (b : Machine k p)
    (f : Fin n → Fin p)
    (step : ∀ q c, f (a.step q c) = b.step (f q) c) :
    ∀ w q, f (run a q w) = run b (f q) w := by
  intro w
  induction w with
  | nil => intro q; rfl
  | cons c w ih =>
    intro q
    change f (run a (a.step q c) w) = run b (b.step (f q) c) w
    rw [ih, step]

theorem accepts_map_iff {k n p : Nat} (a : Machine k n) (b : Machine k p)
    (f : Fin n → Fin p) (initial : f a.start = b.start)
    (step : ∀ q c, f (a.step q c) = b.step (f q) c)
    (final : ∀ q, a.accept q = b.accept (f q)) :
    ∀ w, accepts a w ↔ accepts b w := by
  intro w
  unfold accepts
  rw [final, run_map a b f step, initial]

/-- A checked powerset construction exposes the witnesses hidden by projection. -/
def ProjectionValid {k l n p : Nat} (a : Machine l p) (b : Machine k n)
    (letter : Fin l → Fin k) (states : Fin n → Finset (Fin p)) : Prop :=
  states b.start = {a.start} ∧
  (∀ q d s, s ∈ states (b.step q d) ↔
    ∃ t ∈ states q, ∃ c, letter c = d ∧ a.step t c = s) ∧
  (∀ q, b.accept q = true ↔ ∃ s ∈ states q, a.accept s = true)

instance {k l n p : Nat} (a : Machine l p) (b : Machine k n)
    (letter : Fin l → Fin k) (states : Fin n → Finset (Fin p)) :
    Decidable (ProjectionValid a b letter states) := by
  unfold ProjectionValid
  infer_instance

theorem projection_sound {k l n p : Nat} (a : Machine l p) (b : Machine k n)
    (letter : Fin l → Fin k) (states : Fin n → Finset (Fin p))
    (h : ProjectionValid a b letter states) (w : List (Fin k))
    (hw : accepts b w) : ∃ u, u.map letter = w ∧ accepts a u := by
  have lift : ∀ w q s, s ∈ states (run b q w) →
      ∃ t ∈ states q, ∃ u, u.map letter = w ∧ run a t u = s := by
    intro v
    induction v with
    | nil =>
      intro q s hs
      exact ⟨s, hs, [], rfl, rfl⟩
    | cons d v ih =>
      intro q s hs
      obtain ⟨t, ht, u, hu, hr⟩ := ih (b.step q d) s hs
      obtain ⟨r, hrmem, c, hc, hstep⟩ := (h.2.1 q d t).mp ht
      refine ⟨r, hrmem, c :: u, ?_, ?_⟩
      · simp only [List.map_cons, hc, hu]
      · simpa only [run, hstep] using hr
  obtain ⟨s, hs, hf⟩ := (h.2.2 _).mp hw
  obtain ⟨t, ht, u, hu, hr⟩ := lift w b.start s hs
  rw [h.1, Finset.mem_singleton] at ht
  subst t
  exact ⟨u, hu, by unfold accepts; rw [hr]; exact hf⟩

/-- Soundness of a trimmed product only needs maps on live states. The explicit
sink cannot lead back to an accepting state. -/
def ProductValid {k l n p : Nat} (a : Machine l p) (b : Machine k n)
    (letter : Fin k → Fin l) (state : Fin n → Option (Fin p)) : Prop :=
  state b.start = some a.start ∧
  (∀ q c, (state (b.step q c)).isSome = true →
    ∃ s, state q = some s ∧ state (b.step q c) = some (a.step s (letter c))) ∧
  (∀ q, b.accept q = true → ∃ s, state q = some s ∧ a.accept s = true)

instance {k l n p : Nat} (a : Machine l p) (b : Machine k n)
    (letter : Fin k → Fin l) (state : Fin n → Option (Fin p)) :
    Decidable (ProductValid a b letter state) := by
  unfold ProductValid
  infer_instance

theorem product_sound {k l n p : Nat} (a : Machine l p) (b : Machine k n)
    (letter : Fin k → Fin l) (state : Fin n → Option (Fin p))
    (h : ProductValid a b letter state) (w : List (Fin k))
    (hw : accepts b w) : accepts a (w.map letter) := by
  have lift : ∀ w q s, state (run b q w) = some s →
      ∃ t, state q = some t ∧ run a t (w.map letter) = s := by
    intro v
    induction v with
    | nil => intro q s hs; exact ⟨s, hs, rfl⟩
    | cons c v ih =>
      intro q s hs
      obtain ⟨t, ht, hr⟩ := ih (b.step q c) s hs
      obtain ⟨r, hrq, hstep⟩ := h.2.1 q c (by simp [ht])
      have heq : a.step r (letter c) = t := by simpa [ht] using hstep.symm
      exact ⟨r, hrq, by simpa only [List.map_cons, run, heq] using hr⟩
  obtain ⟨s, hs, hf⟩ := h.2.2 _ hw
  obtain ⟨t, ht, hr⟩ := lift w b.start s hs
  have heq : t = a.start := by simpa [h.1] using ht.symm
  subst t
  unfold accepts
  rw [hr]
  exact hf

def ProjectionCheck {k l n p : Nat} (a : Machine l p) (b : Machine k n)
    (letter : Fin l → Fin k) (states : Fin n → Finset (Fin p)) : Prop :=
  states b.start = {a.start} ∧
  (∀ q d, states (b.step q d) = (states q).biUnion
    (fun t => (Finset.univ.filter (fun c => letter c = d)).image (a.step t))) ∧
  (∀ q, b.accept q = true ↔ ∃ s ∈ states q, a.accept s = true)

instance {k l n p : Nat} (a : Machine l p) (b : Machine k n)
    (letter : Fin l → Fin k) (states : Fin n → Finset (Fin p)) :
    Decidable (ProjectionCheck a b letter states) := by
  unfold ProjectionCheck
  infer_instance

theorem projectionCheck_valid {k l n p : Nat} (a : Machine l p) (b : Machine k n)
    (letter : Fin l → Fin k) (states : Fin n → Finset (Fin p))
    (h : ProjectionCheck a b letter states) : ProjectionValid a b letter states := by
  refine ⟨h.1, ?_, ?_⟩
  · intro q d s
    rw [h.2.1]
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
  · exact h.2.2

def ProductCheck {k l n p : Nat} (a : Machine l p) (b : Machine k n)
    (letter : Fin k → Fin l) (state : Fin n → Option (Fin p)) : Prop :=
  state b.start = some a.start ∧
  (∀ q c, (state (b.step q c)).isSome = true →
    state (b.step q c) = (state q).map (fun s => a.step s (letter c))) ∧
  (∀ q, b.accept q = true → (state q).any (fun s => a.accept s) = true)

instance {k l n p : Nat} (a : Machine l p) (b : Machine k n)
    (letter : Fin k → Fin l) (state : Fin n → Option (Fin p)) :
    Decidable (ProductCheck a b letter state) := by
  unfold ProductCheck
  infer_instance

theorem productCheck_valid {k l n p : Nat} (a : Machine l p) (b : Machine k n)
    (letter : Fin k → Fin l) (state : Fin n → Option (Fin p))
    (h : ProductCheck a b letter state) : ProductValid a b letter state := by
  refine ⟨h.1, ?_, ?_⟩
  · intro q c hc
    have he := h.2.1 q c hc
    cases hq : state q with
    | none => simp [hq] at he; simp [he] at hc
    | some s => exact ⟨s, rfl, by simpa [hq] using he⟩
  · intro q hq
    have hf := h.2.2 q hq
    cases hs : state q with
    | none => simp [hs] at hf
    | some s => exact ⟨s, rfl, by simpa [hs] using hf⟩

/-- Semantic states need not be finite. Only the supplied finite trace labels
and local transition equations are reduced by the kernel. -/
def TraceCheck {k n : Nat} {S : Type} (b : Machine k n)
    (initial : S) (step : S → Fin k → S) (good : S → Bool)
    (state : Fin n → Option S) : Prop :=
  state b.start = some initial ∧
  (∀ q c, (state (b.step q c)).isSome = true →
    state (b.step q c) = (state q).map (fun s => step s c)) ∧
  (∀ q, b.accept q = true → (state q).any good = true)

instance {k n : Nat} {S : Type} [DecidableEq S] (b : Machine k n)
    (initial : S) (step : S → Fin k → S) (good : S → Bool)
    (state : Fin n → Option S) : Decidable (TraceCheck b initial step good state) := by
  unfold TraceCheck
  infer_instance

theorem trace_sound {k n : Nat} {S : Type} (b : Machine k n)
    (initial : S) (step : S → Fin k → S) (good : S → Bool)
    (state : Fin n → Option S) (h : TraceCheck b initial step good state)
    (w : List (Fin k)) (hw : accepts b w) : good (w.foldl step initial) = true := by
  have lift : ∀ w q s, state (run b q w) = some s →
      ∃ t, state q = some t ∧ w.foldl step t = s := by
    intro v
    induction v with
    | nil => intro q s hs; exact ⟨s, hs, rfl⟩
    | cons c v ih =>
      intro q s hs
      obtain ⟨t, ht, hr⟩ := ih (b.step q c) s hs
      have he := h.2.1 q c (by simp [ht])
      cases hq : state q with
      | none => simp [hq, ht] at he
      | some r =>
        have heq : step r c = t := by simpa [ht,hq] using he.symm
        exact ⟨r, rfl, by simpa only [List.foldl_cons, heq] using hr⟩
  have hf := h.2.2 _ hw
  cases hs : state (run b b.start w) with
  | none => simp [hs] at hf
  | some s =>
    obtain ⟨t, ht, hr⟩ := lift w b.start s hs
    have heq : t = initial := by simpa [h.1] using ht.symm
    subst t
    rw [hr]
    simpa [hs] using hf

#print axioms valid_implies_inclusion
#print axioms accepts_map_iff

end CloitreCollaboration.Certificate
