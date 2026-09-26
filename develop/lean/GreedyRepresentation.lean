import RecurrenceBridge
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Fin.Basic

set_option autoImplicit false

namespace CloitreCollaboration.Greedy

theorem W_pos (n : Nat) : 0 < W n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | n
      · decide
      · decide
      · decide
      · rw [W]
        have := ih n (by omega)
        have := ih (n + 1) (by omega)
        omega

theorem U_pos (n : Nat) : 0 < U n := by
  cases n with
  | zero => decide
  | succ n => exact W_pos (n + 1)

theorem U_step_gap (n : Nat) : U (n + 6) = U (n + 5) + U (n + 1) := by
  have h1 := U_recurrence (n + 2)
  have h2 := U_recurrence (n + 1)
  have h3 := U_recurrence n
  simp only [Nat.add_assoc, Nat.reduceAdd] at *
  omega

theorem U_succ_lt (n : Nat) : U n < U (n + 1) := by
  rcases n with _ | _ | _ | _ | _ | n
  all_goals try decide
  rw [U_step_gap]
  have := U_pos (n + 1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at *
  omega

theorem U_strictMono : StrictMono U := strictMono_nat_of_lt_succ U_succ_lt

theorem U_index_bound (n : Nat) : (n : Int) + 1 <= U n := by
  induction n with
  | zero => decide
  | succ n ih =>
      have := U_succ_lt n
      omega

def value : List Nat -> Int
  | [] => 0
  | p :: ps => U p + value ps

/-- Allowed separation of successive selected positions, including the bottom exception. -/
def Gap (p q : Nat) : Prop := q + 5 <= p \/ (p = 4 /\ q = 0)

/-- Descending selected positions; zero digits do not occur in this representation. -/
def Admissible : List Nat -> Prop
  | [] => True
  | [_] => True
  | p :: q :: ps => Gap p q /\ Admissible (q :: ps)

theorem gap_lt {p q : Nat} (h : Gap p q) : q < p := by
  rcases h with h | ⟨h, h'⟩ <;> omega

theorem value_nonneg (ps : List Nat) : 0 <= value ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      have := U_pos p
      simp only [value]
      omega

theorem value_head (p : Nat) (ps : List Nat) : U p <= value (p :: ps) := by
  have := value_nonneg ps
  simp only [value]
  omega

theorem admissible_tail {p : Nat} {ps : List Nat} (h : Admissible (p :: ps)) :
    Admissible ps := by
  cases ps with
  | nil => trivial
  | cons q qs => exact h.2

/-- An allowed representation lies in the interval belonging to its largest weight. -/
theorem value_bound (p : Nat) (ps : List Nat) (h : Admissible (p :: ps)) :
    value (p :: ps) < U (p + 1) := by
  induction p using Nat.strong_induction_on generalizing ps with
  | h p ih =>
      cases ps with
      | nil => simpa [value] using U_succ_lt p
      | cons q qs =>
          have hgap := h.1
          have ht := h.2
          have hq := ih q (gap_lt hgap) qs ht
          rcases hgap with hgap | ⟨rfl, rfl⟩
          · have hp : 5 <= p := by omega
            obtain ⟨n, rfl⟩ : exists n, p = n + 5 := ⟨p - 5, by omega⟩
            have hmono : U (q + 1) <= U (n + 1) := U_strictMono.monotone (by omega)
            have hstep := U_step_gap n
            simp only [value] at *
            simp only [Nat.add_assoc, Nat.reduceAdd] at *
            omega
          · have hu : U 1 = 2 := rfl
            have h4 : U 4 = 5 := rfl
            have h5 : U 5 = 7 := rfl
            simp only [value] at *
            norm_num only [Nat.reduceAdd] at *
            omega

/-- At each step the first listed weight is the greatest weight below the remainder. -/
def IsGreedy : List Nat -> Prop
  | [] => True
  | p :: ps => value (p :: ps) < U (p + 1) /\ IsGreedy ps

theorem admissible_isGreedy (ps : List Nat) (h : Admissible ps) : IsGreedy ps := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨value_bound p ps h, ih (admissible_tail h)⟩

theorem isGreedy_admissible (ps : List Nat) (h : IsGreedy ps) : Admissible ps := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
      cases ps with
      | nil => trivial
      | cons q qs =>
          refine ⟨?_, ih h.2⟩
          have hv := h.1
          have hlo := value_head q qs
          have hpositive := U_pos q
          rcases p with _ | _ | _ | _ | _ | p
          · change 1 + value (q :: qs) < 2 at hv
            omega
          · change 2 + value (q :: qs) < 3 at hv
            omega
          · change 3 + value (q :: qs) < 4 at hv
            omega
          · change 4 + value (q :: qs) < 5 at hv
            omega
          · have hq : U q < U 1 := by
              change 5 + value (q :: qs) < 7 at hv
              change U q < 2
              omega
            have hqi : q < 1 := U_strictMono.lt_iff_lt.mp hq
            exact Or.inr ⟨rfl, by omega⟩
          · have hs := U_step_gap p
            have hq : U q < U (p + 1) := by
              change U (p + 5) + value (q :: qs) < U (p + 5 + 1) at hv
              simp only [Nat.add_assoc, Nat.reduceAdd] at hv
              omega
            have hqi : q < p + 1 := U_strictMono.lt_iff_lt.mp hq
            exact Or.inl (by omega)

theorem admissible_iff_isGreedy (ps : List Nat) : Admissible ps <-> IsGreedy ps :=
  ⟨admissible_isGreedy ps, isGreedy_admissible ps⟩

theorem weight_interval_bounded (m : Nat) (n : Int) (hn : 1 <= n)
    (hm : n < U (m + 1)) : exists p, U p <= n /\ n < U (p + 1) := by
  induction m with
  | zero => exact ⟨0, by change 1 <= n; exact hn, hm⟩
  | succ m ih =>
      by_cases h : U (m + 1) <= n
      · exact ⟨m + 1, h, hm⟩
      · exact ih (by omega)

theorem weight_interval (n : Nat) (hn : 0 < n) :
    exists p, U p <= (n : Int) /\ (n : Int) < U (p + 1) := by
  have hb := U_index_bound (n + 1)
  exact weight_interval_bounded n n (by omega) (by omega)

theorem exists_representation (n : Nat) :
    exists ps, Admissible ps /\ value ps = (n : Int) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        exact ⟨[], trivial, rfl⟩
      · obtain ⟨p, hp, hpnext⟩ := weight_interval n (by omega)
        let r := ((n : Int) - U p).toNat
        have hrvalue : (r : Int) = (n : Int) - U p := Int.toNat_of_nonneg (by omega)
        have hpositive := U_pos p
        have hrlt : r < n := by omega
        obtain ⟨ps, hps, hvalue⟩ := ih r hrlt
        have htotal : value (p :: ps) = (n : Int) := by
          simp only [value]
          omega
        refine ⟨p :: ps, isGreedy_admissible _ ?_, htotal⟩
        exact ⟨by rw [htotal]; exact hpnext, admissible_isGreedy ps hps⟩

theorem representation_unique (ps qs : List Nat)
    (hp : Admissible ps) (hq : Admissible qs) (heq : value ps = value qs) : ps = qs := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => rfl
      | cons q qs =>
          have := value_head q qs
          have := U_pos q
          change 0 = value (q :: qs) at heq
          omega
  | cons p ps ih =>
      cases qs with
      | nil =>
          have := value_head p ps
          have := U_pos p
          change value (p :: ps) = 0 at heq
          omega
      | cons q qs =>
          have hpb := value_bound p ps hp
          have hqb := value_bound q qs hq
          have hpl := value_head p ps
          have hql := value_head q qs
          have hpq : p = q := by
            by_contra hne
            rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
            · have := U_strictMono.monotone (show p + 1 <= q by omega)
              omega
            · have := U_strictMono.monotone (show q + 1 <= p by omega)
              omega
          subst q
          have ht : value ps = value qs := by simpa only [value, add_left_cancel_iff] using heq
          rw [ih qs (admissible_tail hp) (admissible_tail hq) ht]

theorem existsUnique_representation (n : Nat) :
    ExistsUnique (fun ps => Admissible ps /\ value ps = (n : Int)) := by
  obtain ⟨ps, hp, hv⟩ := exists_representation n
  refine ⟨ps, ⟨hp, hv⟩, ?_⟩
  intro qs hq
  exact representation_unique qs ps hq.1 hp (hq.2.trans hv.symm)

def bitValue (b : Bool) : Int := if b then 1 else 0

/-- LSD-first digits, converted to descending positions starting at offset k. -/
def positions (k : Nat) : List Bool -> List Nat
  | [] => []
  | b :: bs => positions (k + 1) bs ++ if b then [k] else []

theorem value_append (ps qs : List Nat) : value (ps ++ qs) = value ps + value qs := by
  induction ps with
  | nil => simp [value]
  | cons p ps ih => simp [value, ih, Int.add_assoc]

theorem positions_value (digits : List Bool) (k : Nat) :
    value (positions k digits) = weighted U k (digits.map bitValue) := by
  induction digits generalizing k with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simp [positions, value_append, ih, bitValue, weighted, value, Int.add_comm]

theorem positions_append (bs cs : List Bool) (k : Nat) :
    positions k (bs ++ cs) = positions (k + bs.length) cs ++ positions k bs := by
  induction bs generalizing k with
  | nil => simp [positions]
  | cons b bs ih =>
      simp only [List.cons_append, positions, ih, List.length_cons]
      have hk : k + 1 + bs.length = k + (bs.length + 1) := by omega
      rw [hk, List.append_assoc]

theorem positions_false (n k : Nat) : positions k (List.replicate n false) = [] := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, positions, ih]

/-- Canonical LSD-first binary encoding of a descending admissible position list. -/
def toBits : List Nat -> List Bool
  | [] => []
  | p :: ps => toBits ps ++ List.replicate (p - (toBits ps).length) false ++ [true]

theorem toBits_length (p : Nat) (ps : List Nat) (h : Admissible (p :: ps)) :
    (toBits (p :: ps)).length = p + 1 := by
  induction ps generalizing p with
  | nil => simp [toBits]
  | cons q qs ih =>
      have ht := ih q h.2
      have hl := gap_lt h.1
      simp only [toBits, List.length_append, List.length_replicate, List.length_singleton] at *
      omega

theorem positions_toBits (ps : List Nat) (h : Admissible ps) :
    positions 0 (toBits ps) = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      have ht := admissible_tail h
      have hlen : (toBits ps).length <= p := by
        cases ps with
        | nil => simp [toBits]
        | cons q qs =>
            rw [toBits_length q qs ht]
            have := gap_lt h.1
            omega
      simp only [toBits, positions_append, List.length_append, List.length_replicate,
        Nat.zero_add]
      rw [positions_false, List.nil_append]
      have hoffset : (toBits ps).length + (p - (toBits ps).length) = p := by omega
      rw [hoffset]
      simp only [positions, List.nil_append, if_true]
      exact congrArg (List.cons p) (ih ht)

def BinaryAdmissible (digits : List Bool) : Prop := Admissible (positions 0 digits)

theorem exists_binary (n : Nat) :
    exists digits : List Bool,
      BinaryAdmissible digits /\ weighted U 0 (digits.map bitValue) = (n : Int) := by
  obtain ⟨ps, hp, hv⟩ := exists_representation n
  refine ⟨toBits ps, ?_, ?_⟩
  · unfold BinaryAdmissible
    rw [positions_toBits ps hp]
    exact hp
  · rw [← positions_value, positions_toBits ps hp]
    exact hv

theorem positions_lower (digits : List Bool) (k p : Nat) (hp : p ∈ positions k digits) :
    k <= p := by
  induction digits generalizing k with
  | nil => simp [positions] at hp
  | cons b bs ih =>
      simp only [positions, List.mem_append] at hp
      rcases hp with hp | hp
      · have := ih (k + 1) hp
        omega
      · cases b <;> simp_all

theorem positions_has_base (b : Bool) (bs : List Bool) (k : Nat) :
    k ∈ positions k (b :: bs) <-> b = true := by
  have hnot : k ∉ positions (k + 1) bs := by
    intro h
    have := positions_lower bs (k + 1) k h
    omega
  cases b <;> simp [positions, hnot]

theorem positions_injective_length (bs cs : List Bool) (k : Nat)
    (hlen : bs.length = cs.length) (heq : positions k bs = positions k cs) : bs = cs := by
  induction bs generalizing cs k with
  | nil => simpa using hlen.symm
  | cons b bs ih =>
      cases cs with
      | nil => simp at hlen
      | cons c cs =>
          have hbc : b = c := by
            have hmem : (k ∈ positions k (b :: bs)) = (k ∈ positions k (c :: cs)) := by rw [heq]
            simp only [positions_has_base] at hmem
            cases b <;> cases c <;> simp_all
          subst c
          have htail : positions (k + 1) bs = positions (k + 1) cs := by
            simp only [positions] at heq
            exact List.append_cancel_right heq
          exact congrArg (List.cons b) (ih cs (k + 1) (by simpa using hlen) htail)

/-- Equal-length padded binary words in the greedy language have unique values. -/
theorem binary_unique_of_length (bs cs : List Bool)
    (hb : BinaryAdmissible bs) (hc : BinaryAdmissible cs)
    (hlen : bs.length = cs.length)
    (hvalue : weighted U 0 (bs.map bitValue) = weighted U 0 (cs.map bitValue)) : bs = cs := by
  have heq : positions 0 bs = positions 0 cs := by
    apply representation_unique _ _ hb hc
    simpa only [positions_value] using hvalue
  exact positions_injective_length bs cs 0 hlen heq

theorem gap_trans {p q r : Nat} (hpq : Gap p q) (hqr : Gap q r) : Gap p r := by
  have hqrlt := gap_lt hqr
  rcases hpq with hpq | ⟨hp, hq⟩
  · exact Or.inl (by omega)
  · omega

theorem admissible_head_gap (p : Nat) (ps : List Nat) (h : Admissible (p :: ps)) :
    forall q, q ∈ ps -> Gap p q := by
  induction ps generalizing p with
  | nil => simp
  | cons r rs ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h.1
      · exact gap_trans h.1 (ih r h.2 q hq)

theorem admissible_pairwise (ps : List Nat) (h : Admissible ps) : List.Pairwise Gap ps := by
  induction ps with
  | nil => exact List.Pairwise.nil
  | cons p ps ih =>
      exact List.Pairwise.cons (admissible_head_gap p ps h) (ih (admissible_tail h))

theorem positions_upper (digits : List Bool) (k p : Nat) (hp : p ∈ positions k digits) :
    p < k + digits.length := by
  induction digits generalizing k with
  | nil => simp [positions] at hp
  | cons b bs ih =>
      simp only [positions, List.mem_append] at hp
      rcases hp with hp | hp
      · have := ih (k + 1) hp
        simp only [List.length_cons]
        omega
      · cases b <;> simp_all

def msPositions (digits : List Bool) : List Nat := positions 0 digits.reverse

theorem msPositions_cons (b : Bool) (bs : List Bool) :
    msPositions (b :: bs) = (if b then [bs.length] else []) ++ msPositions bs := by
  simp [msPositions, List.reverse_cons, positions_append, positions]

theorem admissible_virtual (bs : List Bool) (q : Nat) (hq : 4 <= q) :
    Admissible ((bs.length + q) :: msPositions bs) <-> Admissible (msPositions bs) := by
  cases hps : msPositions bs with
  | nil => trivial
  | cons p ps =>
      have hp : p < bs.length := by
        have hmem : p ∈ positions 0 bs.reverse := by
          change p ∈ msPositions bs
          rw [hps]
          exact List.mem_cons_self
        have := positions_upper bs.reverse 0 p hmem
        simpa using this
      have hg : Gap (bs.length + q) p := Or.inl (by omega)
      change (Gap (bs.length + q) p /\ Admissible (p :: ps)) <-> Admissible (p :: ps)
      exact and_iff_right hg

/-- Seven-state completion of the six-state partial greedy recognizer.
States 0..4 count trailing zeros (capped at four), 5 is terminal-only, 6 rejects. -/
def dfaStep (q : Fin 7) (b : Bool) : Fin 7 :=
  if q.val < 5 then
    if b then (if q.val = 4 then 0 else if q.val = 3 then 5 else 6)
    else ⟨min 4 (q.val + 1), by omega⟩
  else 6

def dfaRun (q : Fin 7) : List Bool -> Fin 7
  | [] => q
  | b :: bs => dfaRun (dfaStep q b) bs

def AcceptsFrom (q : Fin 7) (bs : List Bool) : Prop := (dfaRun q bs).val < 6

@[simp] theorem fin7_zero : (0 : Fin 7).val = 0 := rfl
@[simp] theorem fin7_one : (1 : Fin 7).val = 1 := rfl
@[simp] theorem fin7_two : (2 : Fin 7).val = 2 := rfl
@[simp] theorem fin7_three : (3 : Fin 7).val = 3 := rfl
@[simp] theorem fin7_four : (4 : Fin 7).val = 4 := rfl
@[simp] theorem fin7_five : (5 : Fin 7).val = 5 := rfl
@[simp] theorem fin7_six : (6 : Fin 7).val = 6 := rfl

theorem run_sink (bs : List Bool) : dfaRun 6 bs = 6 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simpa [dfaRun, dfaStep] using ih

theorem accepts_terminal (bs : List Bool) : AcceptsFrom 5 bs <-> bs = [] := by
  cases bs with
  | nil => change (5 < 6 <-> [] = ([] : List Bool)); simp
  | cons b bs => cases b <;> simp [AcceptsFrom, dfaRun, dfaStep, run_sink]

theorem rejects_sink (bs : List Bool) : ¬ AcceptsFrom 6 bs := by
  simp [AcceptsFrom, run_sink]

theorem dfa_semantics (bs : List Bool) (q : Fin 7) (hq : q.val < 5) :
    AcceptsFrom q bs <-> Admissible ((bs.length + q.val) :: msPositions bs) := by
  induction bs generalizing q with
  | nil =>
      simp [AcceptsFrom, dfaRun, msPositions, positions, Admissible]
      omega
  | cons b bs ih =>
      have hzero : AcceptsFrom 0 bs <-> Admissible (bs.length :: msPositions bs) := by
        simpa using ih 0 (by decide)
      have hfour : AcceptsFrom 4 bs <-> Admissible (msPositions bs) := by
        exact (ih 4 (by decide)).trans (admissible_virtual bs 4 (by decide))
      have hqcases : q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4 := by
        have : q.val = 0 \/ q.val = 1 \/ q.val = 2 \/ q.val = 3 \/ q.val = 4 := by omega
        simpa only [Fin.ext_iff, fin7_zero, fin7_one, fin7_two, fin7_three, fin7_four] using this
      rcases hqcases with rfl | rfl | rfl | rfl | rfl
      all_goals cases b
      all_goals simp only [AcceptsFrom, dfaRun] at *
      all_goals simp only [dfaStep, fin7_zero, fin7_one, fin7_two, fin7_three, fin7_four,
        Nat.reduceLT, Nat.reduceAdd, Nat.reduceEqDiff, if_true, if_false,
        min_self, min_eq_right (show 1 <= 4 by decide), min_eq_right (show 2 <= 4 by decide),
        min_eq_right (show 3 <= 4 by decide), min_eq_left (show 4 <= 5 by decide),
        Bool.false_eq_true, msPositions_cons,
        List.nil_append, List.singleton_append, List.length_cons]
      · simpa [Nat.add_assoc] using ih 1 (by decide)
      · simp [run_sink, Admissible, Gap]
        intro hn hnil
        subst bs
        simp at hn
      · simpa [Nat.add_assoc] using ih 2 (by decide)
      · simp [run_sink, Admissible, Gap]
        intro hn hnil
        subst bs
        simp at hn
      · simpa [Nat.add_assoc] using ih 3 (by decide)
      · simp [run_sink, Admissible, Gap]
        intro hn hnil
        subst bs
        simp at hn
      · simpa [Nat.add_assoc] using ih 4 (by decide)
      · rw [show (dfaRun 5 bs).val < 6 <-> bs = [] from accepts_terminal bs]
        cases bs with
        | nil => simp [Admissible, Gap, msPositions, positions]
        | cons b bs => simp [Admissible, Gap]
      · exact hfour.trans (admissible_virtual bs 5 (by decide)).symm
      · simpa [Admissible, Gap, Nat.add_assoc] using hzero

theorem dfa_accepts_iff (bs : List Bool) :
    AcceptsFrom 4 bs <-> BinaryAdmissible bs.reverse := by
  exact (dfa_semantics bs 4 (by decide)).trans (admissible_virtual bs 4 (by decide))

theorem every_nat_dfa (n : Nat) :
    exists bs : List Bool,
      AcceptsFrom 4 bs /\ weighted U 0 (bs.reverse.map bitValue) = (n : Int) := by
  obtain ⟨digits, ha, hv⟩ := exists_binary n
  refine ⟨digits.reverse, ?_, ?_⟩
  · rw [dfa_accepts_iff, List.reverse_reverse]
    exact ha
  · simpa using hv

theorem leading_zero_acceptance (bs : List Bool) :
    AcceptsFrom 4 (false :: bs) <-> AcceptsFrom 4 bs := by
  rfl

theorem leading_zero_value (bs : List Bool) :
    weighted U 0 ((false :: bs).reverse.map bitValue) =
      weighted U 0 (bs.reverse.map bitValue) := by
  rw [← positions_value, ← positions_value]
  change value (msPositions (false :: bs)) = value (msPositions bs)
  rw [msPositions_cons]
  rfl

#print axioms U_strictMono
#print axioms admissible_iff_isGreedy
#print axioms existsUnique_representation
#print axioms exists_binary
#print axioms binary_unique_of_length
#print axioms dfa_accepts_iff
#print axioms every_nat_dfa

end CloitreCollaboration.Greedy
