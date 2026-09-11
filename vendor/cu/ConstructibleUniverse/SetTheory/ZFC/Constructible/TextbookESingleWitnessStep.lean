/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEConstructible
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FullSkolemHull

/-!
# One internal witness step for a decoded textbook E task

For a decoded task `(n,m)`, `textbookEZFLCarrier U (n+1) m` is now an actual
member of `L`.  This file constructs the corresponding one-task witness step.
Its parameter prefixes are the textbook finite function graphs in `seed^n`.
A candidate `y` extends a prefix graph `p` by the pair `<n,y>`, exactly as in
the projection clause defining `E`.

One fixed first-order formula separates from `U` the canonical least witness
for every nonempty prefix fiber.  Thus both the selected witness set and the
step adjoining it to the seed are actual `LCarrier`s.  This remains a
single decoded task.  No uniform graph in the task variable and no omega
iteration are asserted here.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## The textbook tuple-extension predicate -/

/-- Layout `[relation,prefix,arity,value]`: extending `prefix` by
`<arity,value>` is a member of `relation`. -/
def textbookETupleExtensionFormula : FOFormula 4 :=
  .ex
    (.conj
      (.mem (Fin.last 4) (0 : Fin 4).castSucc)
      (TextbookDefFormula.insertPairEqDeltaAt
        (Fin.last 4)
        (1 : Fin 4).castSucc
        (2 : Fin 4).castSucc
        (3 : Fin 4).castSucc).toFO)

@[simp]
theorem satisfies_textbookETupleExtensionFormula
    (relation prefixGraph arity value : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookETupleExtensionFormula
        ![relation, prefixGraph, arity, value] ↔
      insert (ZFSet.pair arity.1 value.1) prefixGraph.1 ∈ relation.1 := by
  rw [textbookETupleExtensionFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨extended, hextended, heqFormula⟩
    have heq : extended.1 =
        insert (ZFSet.pair arity.1 value.1) prefixGraph.1 := by
      apply (TextbookDefFormula.satisfies_insertPairEqDeltaAt
        (Fin.last 4)
        (1 : Fin 4).castSucc
        (2 : Fin 4).castSucc
        (3 : Fin 4).castSucc
        ![relation.1, prefixGraph.1, arity.1, value.1, extended.1]).mp
      apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookDefFormula.insertPairEqDeltaAt
          (Fin.last 4)
          (1 : Fin 4).castSucc
          (2 : Fin 4).castSucc
          (3 : Fin 4).castSucc)
        ![relation, prefixGraph, arity, value, extended]).mp
      exact heqFormula
    rwa [← heq]
  · intro hextended
    let extended : LCarrier.{u} :=
      ⟨insert (ZFSet.pair arity.1 value.1) prefixGraph.1,
        mem_L_of_mem hextended relation.2⟩
    refine ⟨extended, hextended, ?_⟩
    apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (TextbookDefFormula.insertPairEqDeltaAt
        (Fin.last 4)
        (1 : Fin 4).castSucc
        (2 : Fin 4).castSucc
        (3 : Fin 4).castSucc)
      ![relation, prefixGraph, arity, value, extended]).mpr
    apply (TextbookDefFormula.satisfies_insertPairEqDeltaAt
      (Fin.last 4)
      (1 : Fin 4).castSucc
      (2 : Fin 4).castSucc
      (3 : Fin 4).castSucc
      ![relation.1, prefixGraph.1, arity.1, value.1, extended.1]).mpr
    rfl

/-- The extension predicate placed at arbitrary coordinates. -/
def textbookETupleExtensionAt {n : Nat}
    (relation prefixGraph arity value : Fin n) : FOFormula n :=
  FOFormula.rename ![relation, prefixGraph, arity, value]
    textbookETupleExtensionFormula

@[simp]
theorem satisfies_textbookETupleExtensionAt {n : Nat}
    (relation prefixGraph arity value : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (textbookETupleExtensionAt relation prefixGraph arity value) s ↔
      insert (ZFSet.pair (s arity).1 (s value).1) (s prefixGraph).1 ∈
        (s relation).1 := by
  rw [textbookETupleExtensionAt, FOFormula.satisfies_rename]
  have hassign :
      (fun i => s (![relation, prefixGraph, arity, value] i)) =
        ![s relation, s prefixGraph, s arity, s value] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign, satisfies_textbookETupleExtensionFormula]

/-! ## One internally represented candidate fiber -/

/-- Candidates in `U` for one represented relation and one textbook prefix. -/
def textbookEWitnessCandidates
    (U relation prefixGraph arity : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    textbookETupleExtensionFormula ![relation, prefixGraph, arity] U)

@[simp]
theorem mem_textbookEWitnessCandidates_iff
    (U relation prefixGraph arity y : LCarrier.{u}) :
    y.1 ∈ (textbookEWitnessCandidates U relation prefixGraph arity).1 ↔
      y.1 ∈ U.1 ∧
        insert (ZFSet.pair arity.1 y.1) prefixGraph.1 ∈ relation.1 := by
  rw [textbookEWitnessCandidates]
  rw [Classical.choose_spec (exists_separationLCarrier
    textbookETupleExtensionFormula ![relation, prefixGraph, arity] U) y]
  rw [show snoc ![relation, prefixGraph, arity] y =
      ![relation, prefixGraph, arity, y] by
    funext i
    fin_cases i <;> rfl]
  rw [satisfies_textbookETupleExtensionFormula]

theorem textbookEWitnessCandidates_subset
    (U relation prefixGraph arity : LCarrier.{u}) :
    (textbookEWitnessCandidates U relation prefixGraph arity).1 ⊆ U.1 := by
  intro y hy
  let yL : LCarrier.{u} :=
      ⟨y, mem_L_of_mem hy
      (textbookEWitnessCandidates U relation prefixGraph arity).2⟩
  exact (mem_textbookEWitnessCandidates_iff
    U relation prefixGraph arity yL).mp hy |>.1

/-- A nonempty textbook E fiber has a unique least candidate in the
canonical internal stage order. -/
theorem existsUnique_textbookEWitnessMinimum
    (U relation prefixGraph arity : LCarrier.{u})
    (hnonempty : ∃ y : LCarrier.{u},
      y.1 ∈ (textbookEWitnessCandidates U relation prefixGraph arity).1) :
    ∃! y : LCarrier.{u},
      y.1 ∈ (textbookEWitnessCandidates U relation prefixGraph arity).1 ∧
        ∀ z : LCarrier.{u},
          z.1 ∈ (textbookEWitnessCandidates U relation prefixGraph arity).1 →
            ¬ GraphRel (canonicalWitnessOrder U) z y := by
  have hsub : ∀ z : LCarrier.{u},
      z.1 ∈ (textbookEWitnessCandidates U relation prefixGraph arity).1 →
        z.1 ∈ (canonicalWitnessStage U).1 := by
    intro z hz
    exact seed_subset_canonicalWitnessStage U
      (textbookEWitnessCandidates_subset U relation prefixGraph arity hz)
  rcases exists_unique_graph_minimum
      (canonicalWitnessOrder_internallyWellOrders U) hsub hnonempty with
    ⟨y, hy, hunique⟩
  exact ⟨y, hy, fun y' hy' => hunique y' hy'⟩

/-! ## Simultaneous selection over all seed prefixes for one task -/

/-- The internally represented family of textbook prefix graphs `seed^n`. -/
def textbookEWitnessPrefixFamily
    (seed : LCarrier.{u}) (arity : Nat) : LCarrier.{u} :=
  ⟨textbookTupleSpace seed.1 arity,
    textbookTupleSpace_mem_L seed.2 arity⟩

@[simp]
theorem textbookEWitnessPrefixFamily_val
    (seed : LCarrier.{u}) (arity : Nat) :
    (textbookEWitnessPrefixFamily seed arity).1 =
      textbookTupleSpace seed.1 arity :=
  rfl

/-- Layout `[U,relation,prefixes,order,arity,y]`.  Some prefix in the
internal family has `y` as its canonical least E-witness. -/
def textbookEWitnessSelectionFormula : FOFormula 6 :=
  .ex
    (.conj
      (.mem (Fin.last 6) (2 : Fin 6).castSucc)
      (.conj
        (textbookETupleExtensionAt
          (1 : Fin 6).castSucc
          (Fin.last 6)
          (4 : Fin 6).castSucc
          (5 : Fin 6).castSucc)
        (.all
          (FOFormula.imp
            (.conj
              (.mem (Fin.last 7) (0 : Fin 7).castSucc)
              (textbookETupleExtensionAt
                (1 : Fin 7).castSucc
                (Fin.last 6).castSucc
                (4 : Fin 7).castSucc
                (Fin.last 7)))
            (.neg
              (graphRelAt
                (3 : Fin 7).castSucc
                (Fin.last 7)
                (5 : Fin 7).castSucc))))))

@[simp]
theorem satisfies_textbookEWitnessSelectionFormula
    (U relation prefixes order arity y : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookEWitnessSelectionFormula
        ![U, relation, prefixes, order, arity, y] ↔
      ∃ prefixGraph : LCarrier.{u}, prefixGraph.1 ∈ prefixes.1 ∧
        insert (ZFSet.pair arity.1 y.1) prefixGraph.1 ∈ relation.1 ∧
          ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
            insert (ZFSet.pair arity.1 z.1) prefixGraph.1 ∈ relation.1 →
              ¬ GraphRel order z y := by
  simp only [textbookEWitnessSelectionFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_textbookETupleExtensionAt, satisfies_graphRelAt,
    snoc_last, snoc_castSucc]
  apply exists_congr
  intro prefixGraph
  apply and_congr_right
  intro _hprefix
  apply and_congr_right
  intro _hy
  constructor
  · intro hminimal z hzU hzRelation
    exact hminimal z ⟨hzU, hzRelation⟩
  · intro hminimal z
    rintro ⟨hzU, hzRelation⟩
    exact hminimal z hzU hzRelation

/-- The canonical witnesses for every nonempty prefix fiber of one decoded
`E` task, constructed by Separation from `U`. -/
def textbookECanonicalWitnessSelection
    (seed U : LCarrier.{u}) (arity code : Nat) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    textbookEWitnessSelectionFormula
    ![U, textbookEZFLCarrier U (arity + 1) code,
      textbookEWitnessPrefixFamily seed arity,
      canonicalWitnessOrder U,
      ⟨natCode arity, natCode_mem_L arity⟩]
    U)

@[simp]
theorem mem_textbookECanonicalWitnessSelection_iff
    (seed U : LCarrier.{u}) (arity code : Nat) (y : LCarrier.{u}) :
    y.1 ∈ (textbookECanonicalWitnessSelection seed U arity code).1 ↔
      y.1 ∈ U.1 ∧
        ∃ prefixGraph : LCarrier.{u},
          prefixGraph.1 ∈ (textbookEWitnessPrefixFamily seed arity).1 ∧
            insert (ZFSet.pair (natCode arity) y.1) prefixGraph.1 ∈
                (textbookEZFLCarrier U (arity + 1) code).1 ∧
              ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
                insert (ZFSet.pair (natCode arity) z.1) prefixGraph.1 ∈
                    (textbookEZFLCarrier U (arity + 1) code).1 →
                  ¬ GraphRel (canonicalWitnessOrder U) z y := by
  rw [textbookECanonicalWitnessSelection]
  rw [Classical.choose_spec (exists_separationLCarrier
    textbookEWitnessSelectionFormula
    ![U, textbookEZFLCarrier U (arity + 1) code,
      textbookEWitnessPrefixFamily seed arity,
      canonicalWitnessOrder U,
      ⟨natCode arity, natCode_mem_L arity⟩]
    U) y]
  rw [show snoc
      ![U, textbookEZFLCarrier U (arity + 1) code,
        textbookEWitnessPrefixFamily seed arity,
        canonicalWitnessOrder U,
        ⟨natCode arity, natCode_mem_L arity⟩] y =
      ![U, textbookEZFLCarrier U (arity + 1) code,
        textbookEWitnessPrefixFamily seed arity,
        canonicalWitnessOrder U,
        ⟨natCode arity, natCode_mem_L arity⟩, y] by
    funext i
    fin_cases i <;> rfl]
  rw [satisfies_textbookEWitnessSelectionFormula]

/-- Retain the seed and adjoin all canonical witnesses for one decoded task. -/
def textbookESingleWitnessStep
    (seed U : LCarrier.{u}) (arity code : Nat) : LCarrier.{u} :=
  unionLCarrier seed
    (textbookECanonicalWitnessSelection seed U arity code)

theorem seed_subset_textbookESingleWitnessStep
    (seed U : LCarrier.{u}) (arity code : Nat) :
    seed.1 ⊆ (textbookESingleWitnessStep seed U arity code).1 := by
  intro x hx
  let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx seed.2⟩
  exact (mem_unionLCarrier_iff seed
    (textbookECanonicalWitnessSelection seed U arity code) xL).mpr
      (Or.inl hx)

theorem textbookESingleWitnessStep_subset
    {seed U : LCarrier.{u}} (hseed : seed.1 ⊆ U.1)
    (arity code : Nat) :
    (textbookESingleWitnessStep seed U arity code).1 ⊆ U.1 := by
  intro x hx
  let xL : LCarrier.{u} :=
    ⟨x, mem_L_of_mem hx (textbookESingleWitnessStep seed U arity code).2⟩
  rcases (mem_unionLCarrier_iff seed
      (textbookECanonicalWitnessSelection seed U arity code) xL).mp hx with
    hxSeed | hxSelected
  · exact hseed hxSeed
  · exact (mem_textbookECanonicalWitnessSelection_iff
      seed U arity code xL).mp hxSelected |>.1

private theorem textbookTupleGraph_change_codomain
    {seed U : ZFSet.{u}} {arity : Nat}
    (params : Tuple (ZFCarrier U) arity)
    (hparams : ∀ i, (params i).1 ∈ seed) :
    textbookTupleGraph (fun i => ⟨(params i).1, hparams i⟩) =
      textbookTupleGraph params := by
  apply ZFSet.ext
  intro q
  rw [mem_textbookTupleGraph_iff, mem_textbookTupleGraph_iff]

/-- Exact one-task witness closure.  Every seed-parameter fiber which is
nonempty in `U` has a witness in the internally represented single-task
step, and that witness satisfies the same textbook E relation. -/
theorem exists_witness_mem_textbookESingleWitnessStep
    {seed U : LCarrier.{u}} {arity code : Nat}
    (params : Tuple (ZFCarrier U.1) arity)
    (hparams : ∀ i, (params i).1 ∈ seed.1)
    (hexists : ∃ x : ZFCarrier U.1,
      textbookTupleGraph (snoc params x) ∈
        textbookEZF U.1 (natCode (arity + 1)) (natCode code)) :
    ∃ y : ZFCarrier U.1,
      y.1 ∈ (textbookESingleWitnessStep seed U arity code).1 ∧
        textbookTupleGraph (snoc params y) ∈
          textbookEZF U.1 (natCode (arity + 1)) (natCode code) := by
  let paramsSeed : Tuple (ZFCarrier seed.1) arity :=
    fun i => ⟨(params i).1, hparams i⟩
  have hprefixEq : textbookTupleGraph paramsSeed =
      textbookTupleGraph params :=
    textbookTupleGraph_change_codomain params hparams
  let prefixGraph : LCarrier.{u} :=
    ⟨textbookTupleGraph params,
      textbookTupleGraph_mem_L U.2 params⟩
  let relation : LCarrier.{u} :=
    textbookEZFLCarrier U (arity + 1) code
  let arityL : LCarrier.{u} :=
    ⟨natCode arity, natCode_mem_L arity⟩
  have hprefixFamily :
      prefixGraph.1 ∈ (textbookEWitnessPrefixFamily seed arity).1 := by
    change textbookTupleGraph params ∈ textbookTupleSpace seed.1 arity
    rw [← hprefixEq]
    exact textbookTupleGraph_mem_tupleSpace paramsSeed
  rcases hexists with ⟨x, hxRelation⟩
  let xL : LCarrier.{u} := ⟨x.1, mem_L_of_mem x.2 U.2⟩
  have hxExtension :
      insert (ZFSet.pair arityL.1 xL.1) prefixGraph.1 ∈ relation.1 := by
    change insert (ZFSet.pair (natCode arity) x.1)
        (textbookTupleGraph params) ∈
      textbookEZF U.1 (natCode (arity + 1)) (natCode code)
    simpa only [textbookTupleGraph_snoc, textbookTupleSnocGraph] using
      hxRelation
  have hxCandidate :
      xL.1 ∈ (textbookEWitnessCandidates
        U relation prefixGraph arityL).1 :=
    (mem_textbookEWitnessCandidates_iff
      U relation prefixGraph arityL xL).mpr ⟨x.2, hxExtension⟩
  rcases existsUnique_textbookEWitnessMinimum
      U relation prefixGraph arityL ⟨xL, hxCandidate⟩ with
    ⟨y, hyMinimum, _hyUnique⟩
  have hyCandidate := hyMinimum.1
  have hyData := (mem_textbookEWitnessCandidates_iff
    U relation prefixGraph arityL y).mp hyCandidate
  let yU : ZFCarrier U.1 := ⟨y.1, hyData.1⟩
  have hySelected :
      y.1 ∈ (textbookECanonicalWitnessSelection
        seed U arity code).1 := by
    apply (mem_textbookECanonicalWitnessSelection_iff
      seed U arity code y).mpr
    refine ⟨hyData.1, prefixGraph, hprefixFamily, hyData.2, ?_⟩
    intro z hzU hzRelation
    apply hyMinimum.2 z
    exact (mem_textbookEWitnessCandidates_iff
      U relation prefixGraph arityL z).mpr ⟨hzU, hzRelation⟩
  have hyStep :
      y.1 ∈ (textbookESingleWitnessStep seed U arity code).1 := by
    exact (mem_unionLCarrier_iff seed
      (textbookECanonicalWitnessSelection seed U arity code) y).mpr
        (Or.inr hySelected)
  refine ⟨yU, hyStep, ?_⟩
  change textbookTupleGraph (snoc params yU) ∈ relation.1
  rw [textbookTupleGraph_snoc]
  exact hyData.2

end

end Constructible.Model
