import GreedyRepresentation
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

namespace CloitreCollaboration.Morphic

def expand {A B : Type} (f : A -> List B) (w : List A) : List B := w.flatMap f

theorem expand_append {A B : Type} (f : A -> List B) (v w : List A) :
    expand f (v ++ w) = expand f v ++ expand f w := by simp [expand]

theorem expand_comp {A B C : Type} (f : A -> List B) (g : B -> List C) (w : List A) :
    expand g (expand f w) = expand (fun a => expand g (f a)) w := by
  simp [expand, List.flatMap_assoc]

def iterate {A : Type} (f : A -> List A) : Nat -> List A -> List A
  | 0, w => w
  | n + 1, w => expand f (iterate f n w)

theorem iterate_append {A : Type} (f : A -> List A) (n : Nat) (v w : List A) :
    iterate f n (v ++ w) = iterate f n v ++ iterate f n w := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate, ih, expand_append]

theorem intertwine_iterates {A B : Type} (f : A -> List A) (g : B -> List B)
    (p : A -> List B) (h : forall a, expand p (f a) = expand g (p a))
    (n : Nat) (w : List A) :
    expand p (iterate f n w) = iterate g n (expand p w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iterate, expand_comp]
      simp only [h]
      rw [← expand_comp, ih]

theorem expand_prefix {A B : Type} (f : A -> List B) {v w : List A}
    (h : v <+: w) : expand f v <+: expand f w := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨expand f t, (expand_append f v t).symm⟩

theorem iterate_prefix {A : Type} (f : A -> List A) (seed : A)
    (h : [seed] <+: f seed) (n : Nat) :
    iterate f n [seed] <+: iterate f (n + 1) [seed] := by
  induction n with
  | zero => simpa [iterate, expand] using h
  | succ n ih => exact expand_prefix f ih

/-- The marker is 0; letters 1 through 27 retain Cloitre's D-state labels. -/
def mu (q : Fin 28) : List (Fin 28) :=
  match q.val with
  | 0 => [0, 1]
  | 1 => [2]
  | 2 => [3]
  | 3 => [4]
  | 4 => [5, 6]
  | 5 => [7, 8]
  | 6 => []
  | 7 => [9, 10]
  | 8 => [11]
  | 9 => [5, 12]
  | 10 => [13]
  | 11 => [14]
  | 12 => [15]
  | 13 => [16]
  | 14 => [17]
  | 15 => [18]
  | 16 => [19]
  | 17 => [20, 21]
  | 18 => [22]
  | 19 => [23, 21]
  | 20 => [24, 1]
  | 21 => []
  | 22 => [9, 21]
  | 23 => [25, 10]
  | 24 => [26, 1]
  | 25 => [20, 27]
  | 26 => [23, 8]
  | 27 => [15]
  | _ => []

def output (q : Fin 28) : Bool :=
  q.val ∈ [0, 2, 4, 5, 8, 9, 10, 14, 15, 16, 18, 21, 23, 24, 27]

/-- The 26-letter alphabet omits exactly the two terminal letters 6 and 21. -/
def embed (a : Fin 26) : Fin 28 :=
  ⟨a.val + (if 6 <= a.val then 1 else 0) + (if 20 <= a.val then 1 else 0), by split_ifs <;> omega⟩

def project (q : Fin 28) : List (Fin 26) :=
  if q.val = 6 \/ q.val = 21 then []
  else [⟨q.val - (if 6 < q.val then 1 else 0) - (if 21 < q.val then 1 else 0), by split_ifs <;> omega⟩]

def nu (a : Fin 26) : List (Fin 26) := expand project (mu (embed a))

def h (a : Fin 26) : List (Fin 28) := mu (embed a)

def eta (a : Fin 26) : List Bool := (h a).map output

theorem project_embed : forall a : Fin 26, project (embed a) = [a] := by decide

theorem project_mu : forall q : Fin 28,
    expand project (mu q) = expand nu (project q) := by decide

theorem h_project : forall q : Fin 28, expand h (project q) = mu q := by decide

theorem nu_nonempty : forall a : Fin 26, nu a ≠ [] := by decide

theorem eta_nonempty : forall a : Fin 26, eta a ≠ [] := by decide

theorem nu_seed : nu 0 = [0, 1] := by decide

theorem projected_iterates (n : Nat) :
    expand project (iterate mu n [0]) = iterate nu n [0] := by
  simpa [expand, project] using intertwine_iterates mu nu project project_mu n [0]

theorem reconstruction_iterates (n : Nat) :
    expand h (iterate nu n [0]) = iterate mu (n + 1) [0] := by
  rw [← projected_iterates, expand_comp]
  simp only [h_project, iterate]

theorem output_iterates (n : Nat) :
    expand eta (iterate nu n [0]) = (iterate mu (n + 1) [0]).map output := by
  rw [← reconstruction_iterates]
  simp only [expand, List.map_flatMap]
  rfl

theorem expand_length_ge {A B : Type} (f : A -> List B)
    (hf : forall a, f a ≠ []) (w : List A) : w.length <= (expand f w).length := by
  induction w with
  | nil => simp [expand]
  | cons a w ih =>
      have hp : 0 < (f a).length := List.length_pos_iff.mpr (hf a)
      simp only [expand, List.flatMap_cons, List.length_append, List.length_cons] at *
      omega

theorem iterate_starts_seed {A : Type} (f : A -> List A) (seed : A) (tail : List A)
    (hf : f seed = seed :: tail) (n : Nat) : exists t, iterate f n [seed] = seed :: t := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨tail ++ expand f t, ?_⟩
      simp [iterate, ht, expand, hf]

theorem nu_length (n : Nat) : n + 1 <= (iterate nu n [0]).length := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
      obtain ⟨t, ht⟩ := iterate_starts_seed nu 0 [1] nu_seed n
      have hlen := expand_length_ge nu nu_nonempty t
      simp only [ht, List.length_cons] at ih
      simp only [iterate, ht, expand, List.flatMap_cons, nu_seed,
        List.cons_append, List.nil_append, List.length_cons]
      change n + 1 + 1 <= (expand nu t).length + 1 + 1
      omega

def outputPrefix (n : Nat) : List Bool := expand eta (iterate nu n [0])

theorem outputPrefix_grows (n : Nat) : n + 1 <= (outputPrefix n).length :=
  (nu_length n).trans (expand_length_ge eta eta_nonempty _)

theorem outputPrefix_nested (n : Nat) : outputPrefix n <+: outputPrefix (n + 1) := by
  exact expand_prefix eta (iterate_prefix nu 0 (by rw [nu_seed]; exact ⟨[1], rfl⟩) n)

theorem prefix_mono {A : Type} (F : Nat -> List A)
    (hF : forall n, F n <+: F (n + 1)) (m n : Nat) (hmn : m <= n) : F m <+: F n := by
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ n hn ih => exact ih.trans (hF n)

theorem prefix_nth_eq {A : Type} [Inhabited A] {xs ys : List A}
    (h : xs <+: ys) (i : Nat) (hi : i < xs.length) : xs[i]! = ys[i]! := by
  have hy : i < ys.length := lt_of_lt_of_le hi h.length_le
  simp only [getElem!_pos, hi, hy]
  exact h.getElem hi

/-- A genuine infinite binary word, not a finite table or bounded prefix claim. -/
def morphicWord (n : Nat) : Bool := (outputPrefix n)[n]!

/-- Every substitution approximant is a prefix of the same infinite output word. -/
theorem morphicWord_prefix (k i : Nat) (hi : i < (outputPrefix k).length) :
    morphicWord i = (outputPrefix k)[i]! := by
  have hile : i < (outputPrefix i).length := by have := outputPrefix_grows i; omega
  have h1 := prefix_nth_eq
    (prefix_mono outputPrefix outputPrefix_nested i (max i k) (le_max_left _ _)) i hile
  have h2 := prefix_nth_eq
    (prefix_mono outputPrefix outputPrefix_nested k (max i k) (le_max_right _ _)) i hi
  exact h1.trans h2.symm

/-- The non-erasing 26-letter presentation codes all erasing-tree approximants. -/
theorem morphicWord_erasing_prefix (k i : Nat)
    (hi : i < (iterate mu (k + 1) [0]).length) :
    morphicWord i = ((iterate mu (k + 1) [0]).map output)[i]! := by
  have hp := output_iterates k
  change outputPrefix k = _ at hp
  rw [← hp]
  apply morphicWord_prefix
  rw [hp, List.length_map]
  exact hi

theorem iterate_succ_right {A : Type} (f : A -> List A) (n : Nat) (w : List A) :
    iterate f (n + 1) w = iterate f n (expand f w) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (expand f) ih

/-- Breadth-first concatenation of the ordered child-tree levels, including marker 0. -/
def breadth : Nat -> List (Fin 28)
  | 0 => [0]
  | n + 1 => breadth n ++ iterate mu n [1]

theorem erasing_iterates_breadth (n : Nat) : iterate mu n [0] = breadth n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ_right]
      change iterate mu n ([0] ++ [1]) = _
      rw [iterate_append, ih]
      rfl

theorem morphicWord_breadth (k i : Nat) (hi : i < (breadth (k + 1)).length) :
    morphicWord i = ((breadth (k + 1)).map output)[i]! := by
  rw [← erasing_iterates_breadth] at hi ⊢
  exact morphicWord_erasing_prefix k i hi

#print axioms project_mu
#print axioms reconstruction_iterates
#print axioms morphicWord_prefix
#print axioms morphicWord_breadth

end CloitreCollaboration.Morphic
