import PrimitiveSemantics
import Generated.Recurrence

set_option autoImplicit false

namespace CloitreCollaboration.Certificate.Composition

open WordArithmetic Primitive Operations

def val {k : Nat} (i : Nat) (w : List (Fin k)) : Int := wordValue (digit i) w

theorem val_map {k l : Nat} (f : Fin k -> Fin l) (i j : Nat)
    (h : forall a, digit i (f a) = digit j a) (w : List (Fin k)) :
    val i (w.map f) = val j w := by
  unfold val wordValue
  rw [← List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  exact h a

@[simp] theorem SuccessorLetter_val1 (w : List (Fin 8)) :
    val 1 (w.map SuccessorLetter) = val 0 w :=
  val_map SuccessorLetter 1 0 (by decide) w

@[simp] theorem SuccessorLetter_val0 (w : List (Fin 8)) :
    val 0 (w.map SuccessorLetter) = val 2 w :=
  val_map SuccessorLetter 0 2 (by decide) w

@[simp] theorem SuccessorProductPart0Letter_val2 (w : List (Fin 8)) :
    val 2 (w.map SuccessorProductPart0Letter) = val 2 w :=
  val_map SuccessorProductPart0Letter 2 2 (by decide) w

@[simp] theorem SuccessorProductPart0Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map SuccessorProductPart0Letter) = val 1 w :=
  val_map SuccessorProductPart0Letter 1 1 (by decide) w

@[simp] theorem SuccessorProductPart0Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map SuccessorProductPart0Letter) = val 0 w :=
  val_map SuccessorProductPart0Letter 0 0 (by decide) w

@[simp] theorem SuccessorProductPart1Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map SuccessorProductPart1Letter) = val 1 w :=
  val_map SuccessorProductPart1Letter 0 1 (by decide) w

@[simp] theorem PredBLetter_val1 (w : List (Fin 8)) :
    val 1 (w.map PredBLetter) = val 2 w :=
  val_map PredBLetter 1 2 (by decide) w

@[simp] theorem PredBLetter_val0 (w : List (Fin 8)) :
    val 0 (w.map PredBLetter) = val 0 w :=
  val_map PredBLetter 0 0 (by decide) w

@[simp] theorem PredBProductPart0Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map PredBProductPart0Letter) = val 2 w :=
  val_map PredBProductPart0Letter 1 2 (by decide) w

@[simp] theorem PredBProductPart0Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map PredBProductPart0Letter) = val 1 w :=
  val_map PredBProductPart0Letter 0 1 (by decide) w

@[simp] theorem PredBProductPart1Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map PredBProductPart1Letter) = val 1 w :=
  val_map PredBProductPart1Letter 1 1 (by decide) w

@[simp] theorem PredBProductPart1Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map PredBProductPart1Letter) = val 0 w :=
  val_map PredBProductPart1Letter 0 0 (by decide) w

@[simp] theorem HLetter_val1 (w : List (Fin 8)) :
    val 1 (w.map HLetter) = val 2 w :=
  val_map HLetter 1 2 (by decide) w

@[simp] theorem HLetter_val0 (w : List (Fin 8)) :
    val 0 (w.map HLetter) = val 0 w :=
  val_map HLetter 0 0 (by decide) w

@[simp] theorem HProductPart0Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map HProductPart0Letter) = val 2 w :=
  val_map HProductPart0Letter 1 2 (by decide) w

@[simp] theorem HProductPart0Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map HProductPart0Letter) = val 1 w :=
  val_map HProductPart0Letter 0 1 (by decide) w

@[simp] theorem HProductPart1Letter_val2 (w : List (Fin 8)) :
    val 2 (w.map HProductPart1Letter) = val 0 w :=
  val_map HProductPart1Letter 2 0 (by decide) w

@[simp] theorem HProductPart1Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map HProductPart1Letter) = val 1 w :=
  val_map HProductPart1Letter 1 1 (by decide) w

@[simp] theorem HProductPart1Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map HProductPart1Letter) = val 2 w :=
  val_map HProductPart1Letter 0 2 (by decide) w

@[simp] theorem BHLetter_val1 (w : List (Fin 8)) :
    val 1 (w.map BHLetter) = val 2 w :=
  val_map BHLetter 1 2 (by decide) w

@[simp] theorem BHLetter_val0 (w : List (Fin 8)) :
    val 0 (w.map BHLetter) = val 0 w :=
  val_map BHLetter 0 0 (by decide) w

@[simp] theorem BHProductPart0Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map BHProductPart0Letter) = val 2 w :=
  val_map BHProductPart0Letter 1 2 (by decide) w

@[simp] theorem BHProductPart0Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map BHProductPart0Letter) = val 1 w :=
  val_map BHProductPart0Letter 0 1 (by decide) w

@[simp] theorem BHProductPart1Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map BHProductPart1Letter) = val 1 w :=
  val_map BHProductPart1Letter 1 1 (by decide) w

@[simp] theorem BHProductPart1Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map BHProductPart1Letter) = val 0 w :=
  val_map BHProductPart1Letter 0 0 (by decide) w

@[simp] theorem KLetter_val1 (w : List (Fin 8)) :
    val 1 (w.map KLetter) = val 2 w :=
  val_map KLetter 1 2 (by decide) w

@[simp] theorem KLetter_val0 (w : List (Fin 8)) :
    val 0 (w.map KLetter) = val 0 w :=
  val_map KLetter 0 0 (by decide) w

@[simp] theorem KProductPart0Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map KProductPart0Letter) = val 2 w :=
  val_map KProductPart0Letter 1 2 (by decide) w

@[simp] theorem KProductPart0Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map KProductPart0Letter) = val 1 w :=
  val_map KProductPart0Letter 0 1 (by decide) w

@[simp] theorem KProductPart1Letter_val2 (w : List (Fin 8)) :
    val 2 (w.map KProductPart1Letter) = val 0 w :=
  val_map KProductPart1Letter 2 0 (by decide) w

@[simp] theorem KProductPart1Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map KProductPart1Letter) = val 1 w :=
  val_map KProductPart1Letter 1 1 (by decide) w

@[simp] theorem KProductPart1Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map KProductPart1Letter) = val 2 w :=
  val_map KProductPart1Letter 0 2 (by decide) w

@[simp] theorem BKLetter_val1 (w : List (Fin 8)) :
    val 1 (w.map BKLetter) = val 2 w :=
  val_map BKLetter 1 2 (by decide) w

@[simp] theorem BKLetter_val0 (w : List (Fin 8)) :
    val 0 (w.map BKLetter) = val 0 w :=
  val_map BKLetter 0 0 (by decide) w

@[simp] theorem BKProductPart0Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map BKProductPart0Letter) = val 2 w :=
  val_map BKProductPart0Letter 1 2 (by decide) w

@[simp] theorem BKProductPart0Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map BKProductPart0Letter) = val 1 w :=
  val_map BKProductPart0Letter 0 1 (by decide) w

@[simp] theorem BKProductPart1Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map BKProductPart1Letter) = val 1 w :=
  val_map BKProductPart1Letter 1 1 (by decide) w

@[simp] theorem BKProductPart1Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map BKProductPart1Letter) = val 0 w :=
  val_map BKProductPart1Letter 0 0 (by decide) w

@[simp] theorem RecurrenceLetter_val0 (w : List (Fin 8)) :
    val 0 (w.map RecurrenceLetter) = val 2 w :=
  val_map RecurrenceLetter 0 2 (by decide) w

@[simp] theorem RecurrenceProductPart0Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map RecurrenceProductPart0Letter) = val 2 w :=
  val_map RecurrenceProductPart0Letter 1 2 (by decide) w

@[simp] theorem RecurrenceProductPart0Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map RecurrenceProductPart0Letter) = val 1 w :=
  val_map RecurrenceProductPart0Letter 0 1 (by decide) w

@[simp] theorem RecurrenceProductPart1Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map RecurrenceProductPart1Letter) = val 2 w :=
  val_map RecurrenceProductPart1Letter 1 2 (by decide) w

@[simp] theorem RecurrenceProductPart1Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map RecurrenceProductPart1Letter) = val 0 w :=
  val_map RecurrenceProductPart1Letter 0 0 (by decide) w

@[simp] theorem RecurrenceProductPart2Letter_val2 (w : List (Fin 8)) :
    val 2 (w.map RecurrenceProductPart2Letter) = val 1 w :=
  val_map RecurrenceProductPart2Letter 2 1 (by decide) w

@[simp] theorem RecurrenceProductPart2Letter_val1 (w : List (Fin 8)) :
    val 1 (w.map RecurrenceProductPart2Letter) = val 0 w :=
  val_map RecurrenceProductPart2Letter 1 0 (by decide) w

@[simp] theorem RecurrenceProductPart2Letter_val0 (w : List (Fin 8)) :
    val 0 (w.map RecurrenceProductPart2Letter) = val 2 w :=
  val_map RecurrenceProductPart2Letter 0 2 (by decide) w

variable (b : Int -> Int)
variable (hgraph : forall w, accepts Graph w -> b (val 1 w) = val 0 w)
variable (hadd : forall w, accepts Adder w -> val 2 w + val 1 w = val 0 w)
variable (hone : forall w, accepts One w -> val 0 w = 1)

include hadd hone in
theorem successor_value (w : List (Fin 4)) (hw : accepts Successor w) :
    val 1 w = val 0 w + 1 := by
  obtain ⟨u, rfl, hu⟩ := SuccessorSound w hw
  have ha := hadd _ (SuccessorProductPart0Sound u hu)
  have ho := hone _ (SuccessorProductPart1Sound u hu)
  simp only [SuccessorProductPart0Letter_val2, SuccessorProductPart0Letter_val1,
    SuccessorProductPart0Letter_val0] at ha
  simp only [SuccessorProductPart1Letter_val0] at ho
  simp only [SuccessorLetter_val1, SuccessorLetter_val0]
  omega

include hgraph hadd hone

theorem predB_value (w : List (Fin 4)) (hw : accepts PredB w) :
    val 0 w = b (val 1 w - 1) := by
  obtain ⟨u, rfl, hu⟩ := PredBSound w hw
  have hs := successor_value hadd hone _ (PredBProductPart0Sound u hu)
  have hg := hgraph _ (PredBProductPart1Sound u hu)
  simp only [PredBProductPart0Letter_val1, PredBProductPart0Letter_val0] at hs
  simp only [PredBProductPart1Letter_val1, PredBProductPart1Letter_val0] at hg
  simp only [PredBLetter_val0, PredBLetter_val1]
  rw [show val 2 u - 1 = val 1 u by omega]
  exact hg.symm

theorem h_value (w : List (Fin 4)) (hw : accepts H w) :
    val 0 w = val 1 w - b (val 1 w - 1) := by
  obtain ⟨u, rfl, hu⟩ := HSound w hw
  have hp := predB_value b hgraph hadd hone _ (HProductPart0Sound u hu)
  have ha := hadd _ (HProductPart1Sound u hu)
  simp only [HProductPart0Letter_val0, HProductPart0Letter_val1] at hp
  simp only [HProductPart1Letter_val2, HProductPart1Letter_val1, HProductPart1Letter_val0] at ha
  simp only [HLetter_val0, HLetter_val1]
  omega

theorem bh_value (w : List (Fin 4)) (hw : accepts BH w) :
    val 0 w = b (val 1 w - b (val 1 w - 1)) := by
  obtain ⟨u, rfl, hu⟩ := BHSound w hw
  have hh := h_value b hgraph hadd hone _ (BHProductPart0Sound u hu)
  have hg := hgraph _ (BHProductPart1Sound u hu)
  simp only [BHProductPart0Letter_val0, BHProductPart0Letter_val1] at hh
  simp only [BHProductPart1Letter_val0, BHProductPart1Letter_val1] at hg
  simp only [BHLetter_val0, BHLetter_val1]
  rw [← hh]
  exact hg.symm

theorem k_value (w : List (Fin 4)) (hw : accepts K w) :
    val 0 w = val 1 w - b (val 1 w - b (val 1 w - 1)) := by
  obtain ⟨u, rfl, hu⟩ := KSound w hw
  have hp := bh_value b hgraph hadd hone _ (KProductPart0Sound u hu)
  have ha := hadd _ (KProductPart1Sound u hu)
  simp only [KProductPart0Letter_val0, KProductPart0Letter_val1] at hp
  simp only [KProductPart1Letter_val2, KProductPart1Letter_val1, KProductPart1Letter_val0] at ha
  simp only [KLetter_val0, KLetter_val1]
  omega

theorem bk_value (w : List (Fin 4)) (hw : accepts BK w) :
    val 0 w = b (val 1 w - b (val 1 w - b (val 1 w - 1))) := by
  obtain ⟨u, rfl, hu⟩ := BKSound w hw
  have hh := k_value b hgraph hadd hone _ (BKProductPart0Sound u hu)
  have hg := hgraph _ (BKProductPart1Sound u hu)
  simp only [BKProductPart0Letter_val0, BKProductPart0Letter_val1] at hh
  simp only [BKProductPart1Letter_val0, BKProductPart1Letter_val1] at hg
  simp only [BKLetter_val0, BKLetter_val1]
  rw [← hh]
  exact hg.symm

/-- Soundness of the full nested composition, with ordinary integer subtraction. -/
theorem recurrence_value (w : List (Fin 2)) (hw : accepts Recurrence w) :
    b (val 0 w) = val 0 w - b (val 0 w - b (val 0 w - b (val 0 w - 1))) := by
  obtain ⟨u, rfl, hu⟩ := RecurrenceSound w hw
  have hg := hgraph _ (RecurrenceProductPart0Sound u hu)
  have hb := bk_value b hgraph hadd hone _ (RecurrenceProductPart1Sound u hu)
  have ha := hadd _ (RecurrenceProductPart2Sound u hu)
  simp only [RecurrenceProductPart0Letter_val1, RecurrenceProductPart0Letter_val0] at hg
  simp only [RecurrenceProductPart1Letter_val1, RecurrenceProductPart1Letter_val0] at hb
  simp only [RecurrenceProductPart2Letter_val2, RecurrenceProductPart2Letter_val1,
    RecurrenceProductPart2Letter_val0] at ha
  simp only [RecurrenceLetter_val0]
  omega

#print axioms recurrence_value

end CloitreCollaboration.Certificate.Composition
