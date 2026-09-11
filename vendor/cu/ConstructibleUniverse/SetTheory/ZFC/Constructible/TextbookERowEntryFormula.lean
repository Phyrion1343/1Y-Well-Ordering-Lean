/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEStepLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ReplacementFunctionGraphLCarrier

/-!
# A uniform row-entry formula for the textbook E recursion

With fixed parameters `[a,history,m]`, input `n`, and output `entry`, the
formula in this file asserts

`entry = <<m,n>, textbookEStep(a,<m,n>,history)>`.

At this layer the step predicate is left visible.  Its exact `LCarrier`
semantics is a separate theorem; the present file proves only the exact
coordinate and Kuratowski-pair semantics needed before Replacement can be
applied over internal omega.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Coordinates -/

/-- Rename the step layout `[a,key,history,output]` into the two-witness
context extending `[a,history,m,n,entry]`. -/
def textbookERowStepRename : Fin 4 → Fin 7 :=
  ![(0 : Fin 5).castSucc.castSucc,
    (Fin.last 5).castSucc,
    (1 : Fin 5).castSucc.castSucc,
    Fin.last 6]

theorem comp_textbookERowStepRename
    (a history m n entry key output : LCarrier.{u}) :
  (fun i => snoc (snoc ![a, history, m, n, entry] key) output
      (textbookERowStepRename i)) =
      ![a, key, history, output] := by
  funext i
  fin_cases i
  · change snoc (snoc ![a, history, m, n, entry] key) output
      ((0 : Fin 5).castSucc.castSucc) = a
    rw [snoc_castSucc, snoc_castSucc]
    rfl
  · change snoc (snoc ![a, history, m, n, entry] key) output
      ((Fin.last 5).castSucc) = key
    rw [snoc_castSucc, snoc_last]
  · change snoc (snoc ![a, history, m, n, entry] key) output
      ((1 : Fin 5).castSucc.castSucc) = history
    rw [snoc_castSucc, snoc_castSucc]
    rfl
  · change snoc (snoc ![a, history, m, n, entry] key) output
      (Fin.last 6) = output
    rw [snoc_last]

/-- In the seven-variable witness context, `key = <m,n>`. -/
def textbookERowKeyPairDelta : Delta0Formula 7 :=
  Delta0Formula.kuratowskiPairEqAt
    (Fin.last 5).castSucc
    (2 : Fin 5).castSucc.castSucc
    (3 : Fin 5).castSucc.castSucc

/-- In the same context, `entry = <key,output>`. -/
def textbookERowEntryPairDelta : Delta0Formula 7 :=
  Delta0Formula.kuratowskiPairEqAt
    (4 : Fin 5).castSucc.castSucc
    (Fin.last 5).castSucc
    (Fin.last 6)

@[simp]
theorem satisfies_textbookERowKeyPairDelta
    (a history m n entry key output : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookERowKeyPairDelta.toFO
        (snoc (snoc ![a, history, m, n, entry] key) output) ↔
      key.1 = ZFSet.pair m.1 n.1 := by
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    textbookERowKeyPairDelta,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  change key.1 = ZFSet.pair m.1 n.1 ↔ _
  rfl

@[simp]
theorem satisfies_textbookERowEntryPairDelta
    (a history m n entry key output : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookERowEntryPairDelta.toFO
        (snoc (snoc ![a, history, m, n, entry] key) output) ↔
      entry.1 = ZFSet.pair key.1 output.1 := by
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    textbookERowEntryPairDelta,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  change entry.1 = ZFSet.pair key.1 output.1 ↔ _
  rfl

/-! ## The row-entry formula -/

/-- Layout `[a,history,m,n,entry]`.  The two witnesses are the key and its
step value. -/
def textbookERowEntryFormula : FOFormula 5 :=
  .ex (.ex
    (.conj textbookERowKeyPairDelta.toFO
      (.conj
        (FOFormula.rename textbookERowStepRename
          TextbookEFormula.textbookEStepFormula)
        textbookERowEntryPairDelta.toFO)))

@[simp]
theorem satisfies_textbookERowEntryFormula
    (a history m n entry : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookERowEntryFormula
        ![a, history, m, n, entry] ↔
      ∃ key output : LCarrier.{u},
        key.1 = ZFSet.pair m.1 n.1 ∧
          FOFormula.Satisfies LMem
            TextbookEFormula.textbookEStepFormula
            ![a, key, history, output] ∧
          entry.1 = ZFSet.pair key.1 output.1 := by
  simp only [textbookERowEntryFormula, FOFormula.Satisfies]
  apply exists_congr
  intro key
  apply exists_congr
  intro output
  rw [satisfies_textbookERowKeyPairDelta,
    FOFormula.satisfies_rename,
    comp_textbookERowStepRename,
    satisfies_textbookERowEntryPairDelta]

/-- A unique step output yields a unique row entry.  This is the exact
functionality adapter needed by Replacement over internal omega. -/
theorem existsUnique_textbookERowEntryFormula_of_step
    (a history m n : LCarrier.{u})
    (hstep : ExistsUnique fun output : LCarrier.{u} =>
      FOFormula.Satisfies LMem
        TextbookEFormula.textbookEStepFormula
        ![a, orderedPairLCarrier m n, history, output]) :
    ExistsUnique fun entry : LCarrier.{u} =>
      FOFormula.Satisfies LMem textbookERowEntryFormula
        ![a, history, m, n, entry] := by
  rcases hstep with ⟨output, houtput, houtputUnique⟩
  let key : LCarrier.{u} := orderedPairLCarrier m n
  let entry : LCarrier.{u} := orderedPairLCarrier key output
  refine ⟨entry, ?_, ?_⟩
  · apply (satisfies_textbookERowEntryFormula
      a history m n entry).mpr
    exact ⟨key, output, rfl, houtput, rfl⟩
  · intro other hother
    rcases (satisfies_textbookERowEntryFormula
        a history m n other).mp hother with
      ⟨otherKey, otherOutput, hkey, hotherOutput, hentry⟩
    have hkeyEq : otherKey = key := by
      apply Subtype.ext
      exact hkey
    have houtputEq : otherOutput = output := by
      apply houtputUnique otherOutput
      simpa only [key, hkeyEq] using hotherOutput
    apply Subtype.ext
    rw [hentry, hkeyEq, houtputEq]
    rfl

/-- If the step formula is functional at every internal natural input,
Replacement collects the complete row of history entries as one actual
member of `L`.  The row elements are entries themselves, not pairs of the
form `<n,entry>`. -/
theorem exists_textbookERowEntryFamily
    (a history m : LCarrier.{u})
    (hstep : ∀ n : LCarrier.{u}, n.1 ∈ omegaLCarrier.1 →
      ExistsUnique fun output : LCarrier.{u} =>
        FOFormula.Satisfies LMem
          TextbookEFormula.textbookEStepFormula
          ![a, orderedPairLCarrier m n, history, output]) :
    ∃ row : LCarrier.{u}, ∀ entry : LCarrier.{u},
      entry.1 ∈ row.1 ↔
        ∃ n : LCarrier.{u}, n.1 ∈ omegaLCarrier.1 ∧
          FOFormula.Satisfies LMem textbookERowEntryFormula
            ![a, history, m, n, entry] := by
  have hfun : ∀ n : LCarrier.{u}, n.1 ∈ omegaLCarrier.1 →
      ExistsUnique fun entry : LCarrier.{u} =>
        FOFormula.Satisfies LMem textbookERowEntryFormula
          (snoc (snoc ![a, history, m] n) entry) := by
    intro n hn
    have hunique := existsUnique_textbookERowEntryFormula_of_step
      a history m n (hstep n hn)
    have hassign (entry : LCarrier.{u}) :
        snoc (snoc ![a, history, m] n) entry =
          ![a, history, m, n, entry] := by
      funext i
      fin_cases i <;> rfl
    simpa only [hassign] using hunique
  rcases exists_replacementLCarrier textbookERowEntryFormula
      ![a, history, m] omegaLCarrier hfun with
    ⟨row, hrow⟩
  refine ⟨row, ?_⟩
  intro entry
  rw [hrow]
  apply exists_congr
  intro n
  apply and_congr_right
  intro _hn
  have hassign : snoc (snoc ![a, history, m] n) entry =
      ![a, history, m, n, entry] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

end

end Constructible.Model
