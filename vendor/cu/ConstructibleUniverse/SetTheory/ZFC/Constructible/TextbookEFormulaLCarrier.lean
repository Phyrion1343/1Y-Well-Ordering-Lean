/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookERecursion
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEDomainLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookLocalSolutionLCarrier

/-!
# The public textbook E formula over L

This file unfolds the public formula for `E` over `LCarrier`.  It separates
the purely syntactic work from the later existence and uniqueness proof for
the internal local solution graph.
-/

@[expose] public section

universe u

namespace Constructible

noncomputable section

namespace Model

local notation "LMem" => lCarrierMem

@[simp]
theorem satisfies_textbookERecursionValueFormula_rename_lCarrier
    (s : Tuple LCarrier.{u} 5) :
    FOFormula.Satisfies LMem
        (FOFormula.rename
          TextbookEFormula.textbookERecursionValueParameters
          TextbookEFormula.textbookERecursionValueFormula) s <->
      FOFormula.Satisfies LMem
        TextbookEFormula.textbookERecursionValueFormula
        ![s 0, s 4, s 3] := by
  rw [FOFormula.satisfies_rename]
  have hassignment :
      (fun i => s
        (TextbookEFormula.textbookERecursionValueParameters i)) =
        ![s 0, s 4, s 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]

/-- The quantified key in the public formula is exactly the internal
Kuratowski pair `<m,n>`. -/
@[simp]
theorem satisfies_textbookEZFFormula_lCarrier_iff_recursionValue
    (a n m output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
        ![a, n, m, output] <->
      FOFormula.Satisfies LMem
        TextbookEFormula.textbookERecursionValueFormula
        ![a, orderedPairLCarrier m n, output] := by
  rw [TextbookEFormula.textbookEZFFormula]
  simp only [FOFormula.Satisfies]
  constructor
  · rintro ⟨key, hpairFormula, hrecursionFormula⟩
    have hpair :=
      (satisfies_kuratowskiPairEqAt_lCarrier_generic
        (Fin.last 4) (2 : Fin 5) (1 : Fin 5)
        (snoc ![a, n, m, output] key)).mp hpairFormula
    change key.1 = ZFSet.pair m.1 n.1 at hpair
    have hkey : key = orderedPairLCarrier m n := by
      apply Subtype.ext
      simpa only [orderedPairLCarrier_val] using hpair
    subst key
    have hrenamed :=
      (satisfies_textbookERecursionValueFormula_rename_lCarrier
        (snoc ![a, n, m, output] (orderedPairLCarrier m n))).mp
        hrecursionFormula
    have hassignment :
        ![(snoc ![a, n, m, output] (orderedPairLCarrier m n)) 0,
          (snoc ![a, n, m, output] (orderedPairLCarrier m n)) 4,
          (snoc ![a, n, m, output] (orderedPairLCarrier m n)) 3] =
          ![a, orderedPairLCarrier m n, output] := by
      funext i
      fin_cases i <;> rfl
    rw [hassignment] at hrenamed
    exact hrenamed
  · intro hrecursion
    let key : LCarrier.{u} := orderedPairLCarrier m n
    refine ⟨key, ?_, ?_⟩
    · apply (satisfies_kuratowskiPairEqAt_lCarrier_generic
        (Fin.last 4) (2 : Fin 5) (1 : Fin 5)
        (snoc ![a, n, m, output] key)).mpr
      change key.1 = ZFSet.pair m.1 n.1
      rfl
    · apply
        (satisfies_textbookERecursionValueFormula_rename_lCarrier
          (snoc ![a, n, m, output] key)).mpr
      have hassignment :
          ![(snoc ![a, n, m, output] key) 0,
            (snoc ![a, n, m, output] key) 4,
            (snoc ![a, n, m, output] key) 3] =
            ![a, key, output] := by
        funext i
        fin_cases i <;> rfl
      rw [hassignment]
      simpa only [key] using hrecursion

/-- The recursion-value subformula says precisely that the key is in the
textbook domain and that an internal local solution graph has the displayed
value.  Existence of that graph is not asserted here. -/
@[simp]
theorem satisfies_textbookERecursionValueFormula_lCarrier_iff
    (a key output : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookEFormula.textbookERecursionValueFormula
        ![a, key, output] <->
      key.1 ∈ TextbookEDomain /\
        exists graph : LCarrier.{u},
          FOFormula.Satisfies LMem
            (localSolutionFormula
              TextbookEFormula.textbookEDomainWithParamFormula
              TextbookEFormula.textbookERelationWithParamFormula
              TextbookEFormula.textbookEStepFormula)
            ![a, key, graph] /\
          ZFSet.pair key.1 output.1 ∈ graph.1 := by
  have hclassAssignment : snoc ![a] key = ![a, key] := by
    funext i
    fin_cases i <;> rfl
  have hfullAssignment (z : LCarrier.{u}) :
      snoc ![a, key] z = ![a, key, z] := by
    funext i
    fin_cases i <;> rfl
  rw [TextbookEFormula.textbookERecursionValueFormula]
  simpa only [hclassAssignment, hfullAssignment,
    satisfies_textbookEDomainWithParamFormula_lCarrier] using
    (satisfies_recursionValueFormula_lCarrier_iff
      TextbookEFormula.textbookEDomainWithParamFormula
      TextbookEFormula.textbookERelationWithParamFormula
      TextbookEFormula.textbookEStepFormula ![a] key output)

/-- Exact syntactic reduction of the public formula to an internal local
solution at the key `<m,n>`. -/
@[simp]
theorem satisfies_textbookEZFFormula_lCarrier_iff_localSolution
    (a n m output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
        ![a, n, m, output] <->
      (n.1 ∈ textbookEOmegaZF /\ m.1 ∈ textbookEOmegaZF) /\
        exists graph : LCarrier.{u},
          FOFormula.Satisfies LMem
            (localSolutionFormula
              TextbookEFormula.textbookEDomainWithParamFormula
              TextbookEFormula.textbookERelationWithParamFormula
              TextbookEFormula.textbookEStepFormula)
            ![a, orderedPairLCarrier m n, graph] /\
          ZFSet.pair (ZFSet.pair m.1 n.1) output.1 ∈ graph.1 := by
  rw [satisfies_textbookEZFFormula_lCarrier_iff_recursionValue,
    satisfies_textbookERecursionValueFormula_lCarrier_iff]
  simp only [orderedPairLCarrier_val]
  rw [pair_mem_textbookEDomain_iff]
  constructor
  · rintro ⟨⟨hmOmega, hnOmega⟩, hgraph⟩
    exact ⟨⟨hnOmega, hmOmega⟩, hgraph⟩
  · rintro ⟨⟨hnOmega, hmOmega⟩, hgraph⟩
    exact ⟨⟨hmOmega, hnOmega⟩, hgraph⟩

end Model

end

end Constructible
