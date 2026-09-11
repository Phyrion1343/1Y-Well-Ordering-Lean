/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookRecursionFormula
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Separation
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.VEqualsL

/-!
# Formula-defined restriction graphs in L

For an internally represented graph and one point `top`, Separation selects
exactly those graph pairs whose first coordinate lies in a displayed formula
class and is related to `top` by a displayed formula relation.  The selected
restriction is an actual `LCarrier` and has an exact elementwise semantics.
-/

@[expose] public section

universe u v

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Generic coordinate lemmas -/

theorem satisfies_classFormulaAt_generic
    {A : Type u} (E : A → A → Prop) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (params : Fin n → Fin m) (x : Fin m) (s : Tuple A m) :
    FOFormula.Satisfies E
        (classFormulaAt classFormula params x) s ↔
      FOFormula.Satisfies E classFormula
        (snoc (fun i => s (params i)) (s x)) := by
  rw [classFormulaAt, FOFormula.satisfies_rename]
  have hassign :
      (fun i => s (Fin.lastCases x params i)) =
        snoc (fun i => s (params i)) (s x) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  rw [hassign]

theorem satisfies_relationFormulaAt_generic
    {A : Type u} (E : A → A → Prop) {n m : Nat}
    (relationFormula : FOFormula (n + 2))
    (params : Fin n → Fin m) (left right : Fin m)
    (s : Tuple A m) :
    FOFormula.Satisfies E
        (relationFormulaAt relationFormula params left right) s ↔
      FOFormula.Satisfies E relationFormula
        (snoc (snoc (fun i => s (params i)) (s left)) (s right)) := by
  rw [relationFormulaAt, FOFormula.satisfies_rename]
  have hassign :
      (fun i => s
        (Fin.lastCases right (fun j => Fin.lastCases left params j) i)) =
        snoc (snoc (fun i => s (params i)) (s left)) (s right) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  rw [hassign]

@[simp]
theorem satisfies_kuratowskiPairEqAt_lCarrier_generic {n : Nat}
    (pair left right : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (Delta0Formula.kuratowskiPairEqAt pair left right).toFO s ↔
      (s pair).1 = ZFSet.pair (s left).1 (s right).1 := by
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]

/-! ## The Separation predicate -/

/-- In layout `(params,top,pair)`, the two witnesses are the input and output
coordinates of `pair`. -/
def formulaRestrictionMemberFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2)) : FOFormula (n + 2) :=
  let params : Fin n → Fin (n + 4) :=
    fun i => i.castSucc.castSucc.castSucc.castSucc
  let top : Fin (n + 4) :=
    (Fin.last n).castSucc.castSucc.castSucc
  let pair : Fin (n + 4) :=
    (Fin.last (n + 1)).castSucc.castSucc
  let input : Fin (n + 4) := (Fin.last (n + 2)).castSucc
  let output : Fin (n + 4) := Fin.last (n + 3)
  .ex (.ex
    (.conj
      (Delta0Formula.kuratowskiPairEqAt pair input output).toFO
      (.conj
        (classFormulaAt classFormula params input)
        (relationFormulaAt relationFormula params input top))))

@[simp]
theorem satisfies_formulaRestrictionMemberFormula
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    (top pair : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (formulaRestrictionMemberFormula classFormula relationFormula)
        (snoc (snoc params top) pair) ↔
      ∃ input output : LCarrier.{u},
        pair.1 = ZFSet.pair input.1 output.1 ∧
          FOFormula.Satisfies LMem classFormula
            (snoc params input) ∧
          FOFormula.Satisfies LMem relationFormula
            (snoc (snoc params input) top) := by
  simp only [formulaRestrictionMemberFormula, FOFormula.Satisfies]
  apply exists_congr
  intro input
  apply exists_congr
  intro output
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  let full := snoc (snoc (snoc (snoc params top) pair) input) output
  have hpair : full ((Fin.last (n + 1)).castSucc.castSucc) = pair := by
    simp only [full, snoc_castSucc, snoc_last]
  have hinput : full ((Fin.last (n + 2)).castSucc) = input := by
    simp only [full, snoc_castSucc, snoc_last]
  have houtput : full (Fin.last (n + 3)) = output := by
    simp only [full, snoc_last]
  rw [show
    snoc (snoc (snoc (snoc params top) pair) input) output = full by rfl]
  rw [hpair, hinput, houtput]
  rw [satisfies_classFormulaAt_generic,
    satisfies_relationFormulaAt_generic]
  have hparams :
      (fun i =>
        full
          (i.castSucc.castSucc.castSucc.castSucc)) = params := by
    funext i
    simp only [full, snoc_castSucc]
  have htop :
      full
          ((Fin.last n).castSucc.castSucc.castSucc) = top := by
    simp only [full, snoc_castSucc, snoc_last]
  rw [hparams, hinput, htop]

/-! ## The represented restriction -/

/-- Separation of a constructible graph by the formula-defined predecessor
condition. -/
def formulaRestrictionLCarrier {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    (graph top : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    (formulaRestrictionMemberFormula classFormula relationFormula)
    (snoc params top) graph)

@[simp]
theorem mem_formulaRestrictionLCarrier_iff
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    (graph top pair : LCarrier.{u}) :
    pair.1 ∈ (formulaRestrictionLCarrier
      classFormula relationFormula params graph top).1 ↔
      pair.1 ∈ graph.1 ∧
        ∃ input output : LCarrier.{u},
          pair.1 = ZFSet.pair input.1 output.1 ∧
            FOFormula.Satisfies LMem classFormula
              (snoc params input) ∧
            FOFormula.Satisfies LMem relationFormula
              (snoc (snoc params input) top) := by
  rw [formulaRestrictionLCarrier]
  rw [Classical.choose_spec (exists_separationLCarrier
    (formulaRestrictionMemberFormula classFormula relationFormula)
    (snoc params top) graph) pair]
  rw [satisfies_formulaRestrictionMemberFormula]

/-- Raw membership form of the same restriction specification. -/
theorem mem_formulaRestrictionLCarrier_raw_iff
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    (graph top : LCarrier.{u}) (pair : ZFSet.{u}) :
    pair ∈ (formulaRestrictionLCarrier
      classFormula relationFormula params graph top).1 ↔
      pair ∈ graph.1 ∧
        ∃ input output : LCarrier.{u},
          pair = ZFSet.pair input.1 output.1 ∧
            FOFormula.Satisfies LMem classFormula
              (snoc params input) ∧
            FOFormula.Satisfies LMem relationFormula
              (snoc (snoc params input) top) := by
  constructor
  · intro hpair
    let pairL : LCarrier.{u} :=
      ⟨pair, mem_L_of_mem hpair
        (formulaRestrictionLCarrier
          classFormula relationFormula params graph top).2⟩
    exact (mem_formulaRestrictionLCarrier_iff
      classFormula relationFormula params graph top pairL).mp hpair
  · rintro ⟨hpairGraph, input, output, hpair, hclass, hrelation⟩
    have hpairL : pair ∈ L := mem_L_of_mem hpairGraph graph.2
    let pairL : LCarrier.{u} := ⟨pair, hpairL⟩
    apply (mem_formulaRestrictionLCarrier_iff
      classFormula relationFormula params graph top pairL).mpr
    exact ⟨hpairGraph, input, output, hpair, hclass, hrelation⟩

/-! ## Compatibility with the textbook restriction formula -/

@[simp]
theorem satisfies_restrictionGraphFormulaAt_lCarrier_iff
    {n m : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n → Fin m) (graph top restriction : Fin m)
    (s : Tuple LCarrier.{u} m) :
    FOFormula.Satisfies LMem
        (restrictionGraphFormulaAt classFormula relationFormula
          params graph top restriction) s ↔
      ∀ pair : LCarrier.{u},
        pair.1 ∈ (s restriction).1 ↔
          pair.1 ∈ (s graph).1 ∧
            ∃ input output : LCarrier.{u},
              pair.1 = ZFSet.pair input.1 output.1 ∧
                FOFormula.Satisfies LMem classFormula
                  (snoc (fun i => s (params i)) input) ∧
                FOFormula.Satisfies LMem relationFormula
                  (snoc (snoc (fun i => s (params i)) input) (s top)) := by
  simp only [restrictionGraphFormulaAt,
    FOFormula.satisfies_all, FOFormula.satisfies_biimp,
    FOFormula.Satisfies, satisfies_classFormulaAt_generic,
    satisfies_relationFormulaAt_generic,
    satisfies_kuratowskiPairEqAt_lCarrier_generic,
    snoc_last, snoc_castSucc]

@[simp]
theorem satisfies_restrictionGraphFormula_lCarrier_iff
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    (graph top restriction : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (restrictionGraphFormula classFormula relationFormula)
        (snoc (snoc (snoc params graph) top) restriction) ↔
      ∀ pair : LCarrier.{u},
        pair.1 ∈ restriction.1 ↔
          pair.1 ∈ graph.1 ∧
            ∃ input output : LCarrier.{u},
              pair.1 = ZFSet.pair input.1 output.1 ∧
                FOFormula.Satisfies LMem classFormula
                  (snoc params input) ∧
                FOFormula.Satisfies LMem relationFormula
                  (snoc (snoc params input) top) := by
  simpa only [restrictionGraphFormula, snoc_last, snoc_castSucc] using
    (satisfies_restrictionGraphFormulaAt_lCarrier_iff
      classFormula relationFormula
      (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last n).castSucc.castSucc
      (Fin.last (n + 1)).castSucc
      (Fin.last (n + 2))
      (snoc (snoc (snoc params graph) top) restriction))

/-- The Separation-constructed restriction satisfies the exact textbook
restriction-output formula. -/
theorem formulaRestrictionLCarrier_satisfies_restrictionGraphFormula
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    (graph top : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (restrictionGraphFormula classFormula relationFormula)
        (snoc (snoc (snoc params graph) top)
          (formulaRestrictionLCarrier
            classFormula relationFormula params graph top)) := by
  apply (satisfies_restrictionGraphFormula_lCarrier_iff
    classFormula relationFormula params graph top
    (formulaRestrictionLCarrier
      classFormula relationFormula params graph top)).mpr
  intro pair
  exact mem_formulaRestrictionLCarrier_iff
    classFormula relationFormula params graph top pair

end

end Constructible.Model
