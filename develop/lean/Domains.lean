import ConcreteCertificates
import ConstantSemantics
import RepresentationIndependence

set_option autoImplicit false

namespace CloitreCollaboration.Certificate.Domains

open Concrete Primitive WordArithmetic

def symbol (b : Bool) : Fin 2 := if b then 1 else 0

theorem symbol_digit (b : Bool) : digit 0 (symbol b) = Greedy.bitValue b := by cases b <;> rfl

theorem symbols_value (bs : List Bool) : wordValue (digit 0) (bs.map symbol) =
    wordValue Greedy.bitValue bs := by
  unfold wordValue
  rw [← List.map_reverse, List.map_map]
  simp only [Function.comp_def, symbol_digit]

def graphState (q : Fin 7) : Fin 10 :=
  match q.val with
  | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 7 | 4 => 3 | 5 => 8 | _ => 9

theorem graph_sim_step : forall (q : Fin 7) (b : Bool),
    graphTotalityLeft.step (graphState q) (symbol b) = graphState (Greedy.dfaStep q b) := by decide

theorem graph_sim_run (bs : List Bool) (q : Fin 7) :
    run graphTotalityLeft (graphState q) (bs.map symbol) = graphState (Greedy.dfaRun q bs) := by
  induction bs generalizing q with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons, run, graph_sim_step, Greedy.dfaRun, ih]

theorem graph_domain (bs : List Bool) (h : Greedy.AcceptsFrom 4 bs) :
    accepts graphTotalityLeft ([0,0,0] ++ bs.map symbol) := by
  change graphTotalityLeft.accept (run graphTotalityLeft (graphState 4) (bs.map symbol)) = true
  rw [graph_sim_run]
  have hf : forall q : Fin 7, q.val < 6 -> graphTotalityLeft.accept (graphState q) = true := by decide
  exact hf _ h

theorem bounded_domain (bs : List Bool) (h : Greedy.AcceptsFrom 4 bs) :
    accepts candidateBoundLeft ([0,0,0] ++ bs.map symbol) := graph_domain bs h

def recState (q : Fin 12) : Fin 7 :=
  match q.val with
  | 3 => 4 | 4 => 0 | 5 => 1 | 6 => 2 | 7 => 3 | 8 => 4 | 9 => 5 | 10 => 0 | _ => 6

theorem rec_closed : forall (q : Fin 12) (b : Bool), 3 <= q.val ->
    3 <= (recurrenceLanguageLeft.step q (symbol b)).val := by decide

theorem rec_sim_step : forall (q : Fin 12) (b : Bool), 3 <= q.val ->
    recState (recurrenceLanguageLeft.step q (symbol b)) = Greedy.dfaStep (recState q) b := by decide

theorem rec_sim_run (bs : List Bool) (q : Fin 12) (hq : 3 <= q.val) :
    3 <= (run recurrenceLanguageLeft q (bs.map symbol)).val /\
      recState (run recurrenceLanguageLeft q (bs.map symbol)) = Greedy.dfaRun (recState q) bs := by
  induction bs generalizing q with
  | nil => exact ⟨hq, rfl⟩
  | cons b bs ih =>
      obtain ⟨ha,hb⟩ := ih _ (rec_closed q b hq)
      refine ⟨ha, ?_⟩
      simpa only [List.map_cons, run, rec_sim_step q b hq, Greedy.dfaRun] using hb

theorem rec_large_closed : forall (q : Fin 12) (b : Bool), 5 <= q.val ->
    5 <= (recurrenceLanguageLeft.step q (symbol b)).val := by decide

theorem rec_large_run (bs : List Bool) (q : Fin 12) (hq : 5 <= q.val) :
    5 <= (run recurrenceLanguageLeft q (bs.map symbol)).val := by
  induction bs generalizing q with
  | nil => exact hq
  | cons b bs ih => exact ih _ (rec_large_closed q b hq)

theorem rec_small_value (bs : List Bool)
    (h : (run recurrenceLanguageLeft 3 (bs.map symbol)).val < 5) :
    wordValue Greedy.bitValue bs < 2 := by
  induction bs with
  | nil => change (0 : Int) < 2; decide
  | cons b bs ih =>
      cases b with
      | false =>
          rw [Greedy.wordValue_leading_zero]
          exact ih h
      | true =>
          cases bs with
          | nil => change (1 : Int) < 2; decide
          | cons b bs =>
              have hq : 5 <= (recurrenceLanguageLeft.step 4 (symbol b)).val := by
                cases b <;> decide
              have hb := rec_large_run bs _ hq
              change (run recurrenceLanguageLeft (recurrenceLanguageLeft.step 4 (symbol b))
                (bs.map symbol)).val < 5 at h
              omega

theorem recurrence_domain (bs : List Bool) (h : Greedy.AcceptsFrom 4 bs)
    (hn : 2 <= wordValue Greedy.bitValue bs) :
    accepts recurrenceLanguageLeft ([0,0,0] ++ bs.map symbol) := by
  change recurrenceLanguageLeft.accept (run recurrenceLanguageLeft 3 (bs.map symbol)) = true
  obtain ⟨hq,hmap⟩ := rec_sim_run bs 3 (by decide)
  have hgood : (recState (run recurrenceLanguageLeft 3 (bs.map symbol))).val < 6 := by
    rw [hmap]
    exact h
  have hf : forall q : Fin 12, 3 <= q.val -> (recState q).val < 6 ->
      q.val < 5 \/ recurrenceLanguageLeft.accept q = true := by decide
  rcases hf _ hq hgood with hsmall | hfinal
  · have := rec_small_value bs hsmall
    omega
  · exact hfinal

theorem padded_symbols_value (bs : List Bool) :
    wordValue (digit 0) ([0,0,0] ++ bs.map symbol) = wordValue Greedy.bitValue bs := by
  change wordValue (digit 0) (0 :: 0 :: 0 :: bs.map symbol) = _
  rw [Constants.wordValue_zero_cons _ _ _ (by decide),
    Constants.wordValue_zero_cons _ _ _ (by decide),
    Constants.wordValue_zero_cons _ _ _ (by decide), symbols_value]

theorem every_nat_graph_domain (n : Nat) :
    exists w : List (Fin 2), accepts graphTotalityLeft w /\ wordValue (digit 0) w = (n : Int) := by
  obtain ⟨bs, hb, hv⟩ := Greedy.every_nat_dfa n
  exact ⟨[0,0,0] ++ bs.map symbol, graph_domain bs hb, (padded_symbols_value bs).trans hv⟩

theorem every_nat_recurrence_domain (n : Nat) (hn : 2 <= n) :
    exists w : List (Fin 2), accepts recurrenceLanguageLeft w /\ wordValue (digit 0) w = (n : Int) := by
  obtain ⟨bs, hb, hv⟩ := Greedy.every_nat_dfa n
  have hvalue : wordValue Greedy.bitValue bs = (n : Int) := hv
  exact ⟨[0,0,0] ++ bs.map symbol, recurrence_domain bs hb (by rw [hvalue]; omega),
    (padded_symbols_value bs).trans hv⟩

#print axioms graph_domain
#print axioms recurrence_domain

end CloitreCollaboration.Certificate.Domains
