/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFOmega
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFReplacement
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookRecursionFormula
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceValidity
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteOrdinalSuccessorFormula

/-!
# Internal predecessor closure in transitive ZF models

This file internalizes the finite predecessor layers used in Section 6.1 of
Wang Fangting, *Axiomatic Set Theory*.

There is an essential hypothesis which must not be suppressed.  Ambient
set-likeness together with `PredecessorsClosedIn M A R` says that every
predecessor is an element of `M`; it does **not** say that the set of all
predecessors is itself an element of `M`.  We therefore explicitly assume
that `M` satisfies `setLikeRelationOnFormula`.  Its internal predecessor-set
witness is identified extensionally with `displayedPredecessors` by the two
restricted-absoluteness hypotheses.

At a successor layer, Replacement inside `M` collects the displayed
predecessor sets of the members of the previous layer, and Union inside `M`
then gives the next layer.  No externally indexed union is used to infer
model membership.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

open FiniteSequenceZF

/-! ## Internal displayed predecessor sets -/

/-- The model-internal set-like assertion supplies the actual ambient
displayed predecessor set as an element of the transitive model.

`PredecessorsClosedIn` is used in the reverse extensional-inclusion direction:
an ambient predecessor must first be known to belong to `M` before restricted
satisfaction can see it. -/
theorem displayedPredecessors_mem_of_satisfiesIn_setLike
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (_hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hsetLike : HasSetPredecessorsOn A R)
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {x : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A) :
    displayedPredecessors A R hsetLike x ∈ M := by
  have hinternal :=
    (satisfiesIn_setLikeRelationOnFormula_iff
      (M : Set ZFSet.{u}) classFormula relationFormula params).mp hsetLikeIn
  rcases hinternal.2 x hxM ((hclass x hxM).mpr hxA) with
    ⟨predecessors, hpredecessorsM, hpredecessors⟩
  have hpredecessorsAmbient : IsPredecessorSet A R x predecessors := by
    intro y
    constructor
    · intro hy
      have hyM : y ∈ M := hM.1.mem_trans hy hpredecessorsM
      have hyInternal := (hpredecessors y hyM).mp hy
      exact ⟨(hclass y hyM).mp hyInternal.1,
        (hrelationFormula y hyM x hxM).mp hyInternal.2⟩
    · rintro ⟨hyA, hyx⟩
      have hyM : y ∈ M := hclosedIn x hxM y hyA hyx
      exact (hpredecessors y hyM).mpr
        ⟨(hclass y hyM).mpr hyA,
          (hrelationFormula y hyM x hxM).mpr hyx⟩
  have heq : predecessors = displayedPredecessors A R hsetLike x :=
    eq_displayedPredecessors_of_isPredecessorSet
      hsetLike hxA hpredecessorsAmbient
  rw [← heq]
  exact hpredecessorsM

/-! ## Replacement followed by Union at a successor layer -/

/-- If one predecessor layer belongs to `M`, the next one belongs to `M`.

The proof uses the model's Replacement scheme on the previous layer with
`predecessorSetFormula`, then the model's Union axiom.  The Replacement range
is proved to consist exactly of the displayed predecessor sets indexed by the
previous layer. -/
theorem predecessorLayer_succ_mem_of_mem
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hsetLike : HasSetPredecessorsOn A R)
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {x : ZFSet.{u}} (hxA : x ∈ A) (k : Nat)
    (hLayerM : predecessorLayer A R hsetLike x k ∈ M) :
    predecessorLayer A R hsetLike x (k + 1) ∈ M := by
  let paramsM : Tuple (ZFCarrier M) n :=
    fun i => ⟨params i, hparams i⟩
  let layerM : ZFCarrier M :=
    ⟨predecessorLayer A R hsetLike x k, hLayerM⟩
  have hinternal :=
    (satisfiesIn_setLikeRelationOnFormula_iff
      (M : Set ZFSet.{u}) classFormula relationFormula params).mp hsetLikeIn
  have hfun : forall y : ZFCarrier M, y.1 ∈ layerM.1 ->
      ExistsUnique fun predecessors : ZFCarrier M =>
        SatisfiesIn (M : Set ZFSet.{u})
          (predecessorSetFormula classFormula relationFormula)
          (snoc (snoc (zfCarrierTupleVal paramsM) y.1) predecessors.1) := by
    intro y hyLayer
    have hyA : y.1 ∈ A :=
      predecessorLayer_subset hsetLike hxA k hyLayer
    rcases hinternal.2 y.1 y.2 ((hclass y.1 y.2).mpr hyA) with
      ⟨predecessors, hpredecessorsM, hpredecessors⟩
    let predecessorsM : ZFCarrier M :=
      ⟨predecessors, hpredecessorsM⟩
    have hparamsVal : zfCarrierTupleVal paramsM = params := by
      funext i
      rfl
    refine ⟨predecessorsM, ?_, ?_⟩
    · rw [hparamsVal]
      exact (satisfiesIn_predecessorSetFormula_iff
        (M : Set ZFSet.{u}) classFormula relationFormula params
        y.1 predecessors).mpr hpredecessors
    · intro other hother
      apply Subtype.ext
      apply ZFSet.ext
      intro z
      have hzPredM : z ∈ predecessors -> z ∈ M :=
        fun hz => hM.1.mem_trans hz hpredecessorsM
      have hzOtherM : z ∈ other.1 -> z ∈ M :=
        fun hz => hM.1.mem_trans hz other.2
      rw [hparamsVal] at hother
      have hotherSpec :=
        (satisfiesIn_predecessorSetFormula_iff
          (M : Set ZFSet.{u}) classFormula relationFormula params
          y.1 other.1).mp hother
      constructor
      · intro hz
        exact (hpredecessors z (hzOtherM hz)).mpr
          ((hotherSpec z (hzOtherM hz)).mp hz)
      · intro hz
        exact (hotherSpec z (hzPredM hz)).mpr
          ((hpredecessors z (hzPredM hz)).mp hz)
  let range : ZFSet.{u} := M.sep fun predecessors =>
    exists y : ZFSet.{u}, y ∈ layerM.1 ∧
      SatisfiesIn (M : Set ZFSet.{u})
        (predecessorSetFormula classFormula relationFormula)
        (snoc (snoc (zfCarrierTupleVal paramsM) y) predecessors)
  have hRangeM : range ∈ M := by
    exact satisfiesIn_replacementRange_mem_of_isTransitiveZFModel
      hM (predecessorSetFormula classFormula relationFormula)
        paramsM layerM hfun
  have hUnionM : ZFSet.sUnion range ∈ M :=
    sUnion_mem_of_isTransitiveZFModel hM hRangeM
  have hUnionEq : ZFSet.sUnion range =
      predecessorLayer A R hsetLike x (k + 1) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sUnion, mem_predecessorLayer_succ_iff hsetLike hxA k]
    constructor
    · rintro ⟨predecessors, hpredecessorsRange, hzPred⟩
      rcases ZFSet.mem_sep.mp hpredecessorsRange with
        ⟨hpredecessorsM, y, hyLayer, hpredecessorsFormula⟩
      have hyM : y ∈ M := hM.1.mem_trans hyLayer hLayerM
      have hzM : z ∈ M := hM.1.mem_trans hzPred hpredecessorsM
      have hparamsVal : zfCarrierTupleVal paramsM = params := by
        funext i
        rfl
      rw [hparamsVal] at hpredecessorsFormula
      have hspec :=
        (satisfiesIn_predecessorSetFormula_iff
          (M : Set ZFSet.{u}) classFormula relationFormula params
          y predecessors).mp hpredecessorsFormula
      have hzSemantic := (hspec z hzM).mp hzPred
      exact ⟨y, hyLayer, (hclass z hzM).mp hzSemantic.1,
        (hrelationFormula z hzM y hyM).mp hzSemantic.2⟩
    · rintro ⟨y, hyLayer, hzA, hzy⟩
      have hyM : y ∈ M := hM.1.mem_trans hyLayer hLayerM
      have hzM : z ∈ M := hclosedIn y hyM z hzA hzy
      have hyA : y ∈ A :=
        predecessorLayer_subset hsetLike hxA k hyLayer
      have hPredM : displayedPredecessors A R hsetLike y ∈ M :=
        displayedPredecessors_mem_of_satisfiesIn_setLike
          hM classFormula relationFormula params hparams hclass
          hrelationFormula hsetLike hclosedIn hsetLikeIn hyM hyA
      refine ⟨displayedPredecessors A R hsetLike y, ?_, ?_⟩
      · apply ZFSet.mem_sep.mpr
        refine ⟨hPredM, y, hyLayer, ?_⟩
        have hparamsVal : zfCarrierTupleVal paramsM = params := by
          funext i
          rfl
        rw [hparamsVal]
        apply (satisfiesIn_predecessorSetFormula_iff
          (M : Set ZFSet.{u}) classFormula relationFormula params y
          (displayedPredecessors A R hsetLike y)).mpr
        intro w hwM
        rw [displayedPredecessors_spec hsetLike hyA w]
        exact and_congr (hclass w hwM).symm
          (hrelationFormula w hwM y hyM).symm
      · exact (displayedPredecessors_spec hsetLike hyA z).mpr
          ⟨hzA, hzy⟩
  simpa only [← hUnionEq] using hUnionM

/-- Every finite textbook predecessor layer is an element of `M`.

The induction is external only as a proof of one theorem for each standard
natural number.  The successor construction itself is internal Replacement
followed by internal Union. -/
theorem predecessorLayer_mem_of_isTransitiveZFModel
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hsetLike : HasSetPredecessorsOn A R)
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {x : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A) :
    forall k : Nat, predecessorLayer A R hsetLike x k ∈ M := by
  intro k
  induction k with
  | zero =>
      simpa only [predecessorLayer_zero] using
        displayedPredecessors_mem_of_satisfiesIn_setLike
          hM classFormula relationFormula params hparams hclass
          hrelationFormula hsetLike hclosedIn hsetLikeIn hxM hxA
  | succ k ih =>
      simpa only [Nat.succ_eq_add_one] using
        predecessorLayer_succ_mem_of_mem
          hM classFormula relationFormula params hparams hclass
          hrelationFormula hsetLike hclosedIn hsetLikeIn hxA k ih

/-! ## A uniform first-order finite-history formula -/

private theorem internalPC_satisfiesIn_all_iff
    (M : Set ZFSet.{u}) {m : Nat} (formula : FOFormula (m + 1))
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.all formula) s <->
      forall z : ZFSet.{u}, z ∈ M ->
        SatisfiesIn M formula (snoc s z) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

private theorem internalPC_satisfiesIn_biimp_iff
    (M : Set ZFSet.{u}) {m : Nat} (left right : FOFormula m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.biimp left right) s <->
      (SatisfiesIn M left s <-> SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, FOFormula.imp, FOFormula.disj, SatisfiesIn]
  tauto

private theorem internalPC_satisfiesIn_boundedAll_iff
    (M : Set ZFSet.{u}) {m : Nat} (set : Fin m)
    (formula : FOFormula (m + 1)) (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.boundedAll set formula) s <->
      forall z : ZFSet.{u}, z ∈ M -> z ∈ s set ->
        SatisfiesIn M formula (snoc s z) := by
  classical
  simp only [FOFormula.boundedAll, FOFormula.boundedEx, SatisfiesIn]
  constructor
  · intro h z hzM hzSet
    by_contra hz
    exact h ⟨z, hzM, by simpa using hzSet, hz⟩
  · intro h hex
    rcases hex with ⟨z, hzM, hzSet, hz⟩
    exact hz (h z hzM (by simpa using hzSet))

private theorem internalPC_satisfiesIn_rename_iff
    (M : Set ZFSet.{u}) {n m : Nat} (formula : FOFormula n)
    (rename : Fin n -> Fin m) (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.rename rename formula) s <->
      SatisfiesIn M formula (fun i => s (rename i)) := by
  induction formula generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg formula ih => exact not_congr (ih rename s)
  | conj left right ihLeft ihRight =>
      exact and_congr (ihLeft rename s) (ihRight rename s)
  | ex formula ih =>
      simp only [FOFormula.rename, SatisfiesIn, ih]
      constructor
      · rintro ⟨x, hxM, hformula⟩
        refine ⟨x, hxM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula
      · rintro ⟨x, hxM, hformula⟩
        refine ⟨x, hxM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula

/-- Insert the already verified predecessor-set formula at named coordinates
of a larger context. -/
def predecessorSetFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (top predecessors : Fin m) : FOFormula m :=
  FOFormula.rename
    (Fin.lastCases predecessors
      (fun j => Fin.lastCases top params j))
    (predecessorSetFormula classFormula relationFormula)

@[simp]
theorem satisfiesIn_predecessorSetFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (top predecessors : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M
        (predecessorSetFormulaAt classFormula relationFormula
          params top predecessors) s <->
      forall z : ZFSet.{u}, z ∈ M ->
        (z ∈ s predecessors <->
          SatisfiesIn M classFormula
              (snoc (fun i => s (params i)) z) ∧
            SatisfiesIn M relationFormula
              (snoc (snoc (fun i => s (params i)) z) (s top))) := by
  rw [predecessorSetFormulaAt]
  rw [internalPC_satisfiesIn_rename_iff]
  have hassignment :
      (fun i => s
        (Fin.lastCases predecessors
          (fun j => Fin.lastCases top params j) i)) =
        snoc (snoc (fun i => s (params i)) (s top))
          (s predecessors) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  rw [hassignment,
    satisfiesIn_predecessorSetFormula_iff]

/-- One layer is obtained from the preceding layer by taking the union of
the displayed predecessor sets. -/
def predecessorLayerStepFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (current next : Fin m) : FOFormula m :=
  FOFormula.all <| FOFormula.biimp
    (.mem (Fin.last m) next.castSucc)
    (.ex <| .conj
      (.mem (Fin.last (m + 1)) current.castSucc.castSucc)
      (.conj
        (classFormulaAt classFormula
          (fun i => (params i).castSucc.castSucc)
          (Fin.last m).castSucc)
        (relationFormulaAt relationFormula
          (fun i => (params i).castSucc.castSucc)
          (Fin.last m).castSucc (Fin.last (m + 1)))))

@[simp]
theorem satisfiesIn_predecessorLayerStepFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (current next : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M
        (predecessorLayerStepFormulaAt classFormula relationFormula
          params current next) s <->
      forall z : ZFSet.{u}, z ∈ M ->
        (z ∈ s next <->
          exists y : ZFSet.{u}, y ∈ M ∧ y ∈ s current ∧
            SatisfiesIn M classFormula
              (snoc (fun i => s (params i)) z) ∧
            SatisfiesIn M relationFormula
              (snoc (snoc (fun i => s (params i)) z) y)) := by
  rw [predecessorLayerStepFormulaAt, internalPC_satisfiesIn_all_iff]
  constructor
  · intro h z hzM
    have hz := h z hzM
    rw [internalPC_satisfiesIn_biimp_iff] at hz
    simpa only [SatisfiesIn, satisfiesIn_classFormulaAt_iff,
      satisfiesIn_relationFormulaAt_iff, snoc_last, snoc_castSucc] using hz
  · intro h z hzM
    rw [internalPC_satisfiesIn_biimp_iff]
    simpa only [SatisfiesIn, satisfiesIn_classFormulaAt_iff,
      satisfiesIn_relationFormulaAt_iff, snoc_last, snoc_castSucc] using
      h z hzM

/-- The single-step clause used by a finite predecessor-layer history.

In a context containing `graph` and `index`, it quantifies the successor
index, the current value, and the next value. -/
def predecessorHistoryStepFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (graph index : Fin m) : FOFormula m :=
  .ex <| .conj
    (transitiveZFSuccessorAt (Fin.last m) index.castSucc)
    (.ex <| .conj
      (graphValueFormulaAt graph.castSucc.castSucc
        index.castSucc.castSucc (Fin.last (m + 1)))
      (.ex <| .conj
        (graphValueFormulaAt graph.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc (Fin.last (m + 2)))
        (predecessorLayerStepFormulaAt classFormula relationFormula
          (fun i => (params i).castSucc.castSucc.castSucc)
          (Fin.last (m + 1)).castSucc (Fin.last (m + 2)))))

@[simp]
theorem satisfiesIn_predecessorHistoryStepFormulaAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (graph index : Fin m)
    (s : Tuple ZFSet.{u} m) (hs : forall i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (predecessorHistoryStepFormulaAt classFormula relationFormula
          params graph index) s <->
      exists successor : ZFSet.{u}, successor ∈ (M : Set ZFSet.{u}) ∧
        successor = insert (s index) (s index) ∧
        exists current : ZFSet.{u}, current ∈ (M : Set ZFSet.{u}) ∧
          ZFSet.pair (s index) current ∈ s graph ∧
          exists next : ZFSet.{u}, next ∈ (M : Set ZFSet.{u}) ∧
            ZFSet.pair successor next ∈ s graph ∧
            forall z : ZFSet.{u}, z ∈ (M : Set ZFSet.{u}) ->
              (z ∈ next <->
                exists y : ZFSet.{u}, y ∈ (M : Set ZFSet.{u}) ∧
                  y ∈ current ∧
                  SatisfiesIn (M : Set ZFSet.{u}) classFormula
                    (snoc (fun i => s (params i)) z) ∧
                  SatisfiesIn (M : Set ZFSet.{u}) relationFormula
                    (snoc (snoc (fun i => s (params i)) z) y)) := by
  rw [predecessorHistoryStepFormulaAt]
  simp only [SatisfiesIn]
  constructor
  · rintro ⟨successor, hsuccessorM, hsuccessorFormula,
      current, hcurrentM, hcurrentFormula,
      next, hnextM, hnextFormula, hstep⟩
    have hsSuccessor : forall i, snoc s successor i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hsuccessorM
      · simpa using hs j
    have hsuccessor :=
      (satisfiesIn_transitiveZFSuccessorAt_iff hM
        (Fin.last m) index.castSucc (snoc s successor) hsSuccessor).mp
          hsuccessorFormula
    have hsCurrent : forall i, snoc (snoc s successor) current i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hcurrentM
      · simpa using hsSuccessor j
    have hcurrent :=
      (satisfiesIn_graphValueFormulaAt_iff hM
        graph.castSucc.castSucc index.castSucc.castSucc
        (Fin.last (m + 1)) (snoc (snoc s successor) current)
        hsCurrent).mp hcurrentFormula
    have hsNext : forall i,
        snoc (snoc (snoc s successor) current) next i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hnextM
      · simpa using hsCurrent j
    have hnext :=
      (satisfiesIn_graphValueFormulaAt_iff hM
        graph.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s successor) current) next) hsNext).mp
          hnextFormula
    have hstepRaw :=
      (satisfiesIn_predecessorLayerStepFormulaAt_iff
        (M : Set ZFSet.{u}) classFormula relationFormula
        (fun i => (params i).castSucc.castSucc.castSucc)
        (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s successor) current) next)).mp hstep
    refine ⟨successor, hsuccessorM, ?_, current, hcurrentM, ?_,
      next, hnextM, ?_, ?_⟩
    · simpa only [snoc_last, snoc_castSucc] using hsuccessor
    · simpa only [snoc_last, snoc_castSucc] using hcurrent
    · simpa only [snoc_last, snoc_castSucc] using hnext
    · simpa only [snoc_last, snoc_castSucc] using hstepRaw
  · rintro ⟨successor, hsuccessorM, hsuccessor,
      current, hcurrentM, hcurrent,
      next, hnextM, hnext, hstep⟩
    refine ⟨successor, hsuccessorM, ?_, current, hcurrentM, ?_,
      next, hnextM, ?_, ?_⟩
    · have hsSuccessor : forall i, snoc s successor i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hsuccessorM
        · simpa using hs j
      apply (satisfiesIn_transitiveZFSuccessorAt_iff hM
        (Fin.last m) index.castSucc (snoc s successor) hsSuccessor).mpr
      simpa only [snoc_last, snoc_castSucc] using hsuccessor
    · have hsCurrent : forall i,
          snoc (snoc s successor) current i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hcurrentM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hsuccessorM
          · simpa using hs k
      apply (satisfiesIn_graphValueFormulaAt_iff hM
        graph.castSucc.castSucc index.castSucc.castSucc
        (Fin.last (m + 1)) (snoc (snoc s successor) current)
        hsCurrent).mpr
      simpa only [snoc_last, snoc_castSucc] using hcurrent
    · have hsNext : forall i,
          snoc (snoc (snoc s successor) current) next i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hnextM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hcurrentM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa using hsuccessorM
            · simpa using hs l
      apply (satisfiesIn_graphValueFormulaAt_iff hM
        graph.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s successor) current) next) hsNext).mpr
      simpa only [snoc_last, snoc_castSucc] using hnext
    · apply (satisfiesIn_predecessorLayerStepFormulaAt_iff
        (M : Set ZFSet.{u}) classFormula relationFormula
        (fun i => (params i).castSucc.castSucc.castSucc)
        (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s successor) current) next)).mpr
      simpa only [snoc_last, snoc_castSucc] using hstep

/-! ## The canonical ambient finite history graph -/

/-- Insertion of one element into an internal set is available in every
transitive ZF model, by Pairing and Union. -/
theorem insert_mem_of_isTransitiveZFModel {M x a : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) (ha : a ∈ M) :
    insert x a ∈ M := by
  have hsingleton : ({x} : ZFSet.{u}) ∈ M :=
    singleton_mem_of_isTransitiveZFModel hM hx
  have hpair : ({{x}, a} : ZFSet.{u}) ∈ M :=
    unorderedPair_mem_of_isTransitiveZFModel hM hsingleton ha
  have hunion : ZFSet.sUnion ({{x}, a} : ZFSet.{u}) ∈ M :=
    sUnion_mem_of_isTransitiveZFModel hM hpair
  simpa only [ZFSet.sUnion_pair, ← ZFSet.insert_eq] using hunion

/-- The graph containing `<j,p_j(x)>` for all `j ≤ k`.  The ordered-pair
orientation agrees with `functionGraphOnFormulaAt`: input first, value
second. -/
noncomputable def predecessorLayerHistoryGraph
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) :
    Nat -> ZFSet.{u}
  | 0 => {ZFSet.pair (natCode 0) (predecessorLayer A R hsetLike x 0)}
  | k + 1 =>
      insert
        (ZFSet.pair (natCode (k + 1))
          (predecessorLayer A R hsetLike x (k + 1)))
        (predecessorLayerHistoryGraph A R hsetLike x k)

@[simp]
theorem mem_predecessorLayerHistoryGraph_iff
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u})
    (k : Nat) (q : ZFSet.{u}) :
    q ∈ predecessorLayerHistoryGraph A R hsetLike x k <->
      exists j : Nat, j ≤ k ∧
        q = ZFSet.pair (natCode j)
          (predecessorLayer A R hsetLike x j) := by
  induction k with
  | zero =>
      simp [predecessorLayerHistoryGraph]
  | succ k ih =>
      rw [predecessorLayerHistoryGraph, ZFSet.mem_insert_iff, ih]
      constructor
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨k + 1, le_rfl, rfl⟩
        · exact ⟨j, hj.trans (Nat.le_succ k), rfl⟩
      · rintro ⟨j, hj, rfl⟩
        rcases Nat.eq_or_lt_of_le hj with rfl | hj
        · exact Or.inl rfl
        · exact Or.inr ⟨j, Nat.lt_succ_iff.mp hj, rfl⟩

/-- The canonical finite history graph is itself an element of `M` once all
of its finitely many layer values are. -/
theorem predecessorLayerHistoryGraph_mem_of_layers
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u})
    (hlayers : forall j : Nat,
      predecessorLayer A R hsetLike x j ∈ M) :
    forall k : Nat, predecessorLayerHistoryGraph A R hsetLike x k ∈ M := by
  intro k
  induction k with
  | zero =>
      apply singleton_mem_of_isTransitiveZFModel hM
      apply kuratowskiPair_mem_of_isTransitiveZFModel hM
      · simpa only [natCode] using
          natOrdinal_mem_of_isTransitiveZFModel hM 0
      · exact hlayers 0
  | succ k ih =>
      apply insert_mem_of_isTransitiveZFModel hM
      · apply kuratowskiPair_mem_of_isTransitiveZFModel hM
        · simpa only [natCode] using
            natOrdinal_mem_of_isTransitiveZFModel hM (k + 1)
        · exact hlayers (k + 1)
      · exact ih

/-- Exact raw function-graph semantics of the canonical finite history. -/
theorem predecessorLayerHistoryGraph_isFunctionGraph
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u})
    (hlayers : forall j : Nat,
      predecessorLayer A R hsetLike x j ∈ M) (k : Nat) :
    ((forall input : ZFSet.{u}, input ∈ M ->
        input ∈ natCode (k + 1) ->
        exists value : ZFSet.{u}, value ∈ M ∧
          ZFSet.pair input value ∈
            predecessorLayerHistoryGraph A R hsetLike x k ∧
          forall other : ZFSet.{u}, other ∈ M ->
            ZFSet.pair input other ∈
              predecessorLayerHistoryGraph A R hsetLike x k ->
            other = value) ∧
      forall pair : ZFSet.{u}, pair ∈ M ->
        pair ∈ predecessorLayerHistoryGraph A R hsetLike x k ->
        exists input : ZFSet.{u}, input ∈ M ∧
          input ∈ natCode (k + 1) ∧
          exists value : ZFSet.{u}, value ∈ M ∧
            pair = ZFSet.pair input value) := by
  constructor
  · intro input _hinputM hinput
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt input (k + 1)).mp
        hinput with ⟨j, hj, rfl⟩
    have hjle : j ≤ k := Nat.lt_succ_iff.mp hj
    refine ⟨predecessorLayer A R hsetLike x j, hlayers j, ?_, ?_⟩
    · exact (mem_predecessorLayerHistoryGraph_iff
        hsetLike x k _).mpr ⟨j, hjle, rfl⟩
    · intro other _hotherM hother
      rcases (mem_predecessorLayerHistoryGraph_iff
        hsetLike x k _).mp hother with ⟨l, hl, hpair⟩
      have hparts := ZFSet.pair_inj.mp hpair
      have hjl : j = l := natCode_injective hparts.1
      subst l
      exact hparts.2
  · intro pair _hpairM hpair
    rcases (mem_predecessorLayerHistoryGraph_iff
      hsetLike x k pair).mp hpair with ⟨j, hj, rfl⟩
    refine ⟨natCode j, ?_, ?_,
      predecessorLayer A R hsetLike x j, hlayers j, rfl⟩
    · simpa only [natCode] using
        natOrdinal_mem_of_isTransitiveZFModel hM j
    · apply (IndexedSequenceZF.mem_natCode_iff_exists_lt
        (natCode j) (k + 1)).mpr
      exact ⟨j, Nat.lt_succ_iff.mpr hj, rfl⟩

/-! ## The complete finite-history formula -/

/-- Uniform formula with public layout `(params,top,index,output)`.

It asserts the existence of a function graph on `index ∪ {index}`, whose
zero value is the displayed predecessor set of `top`, whose successive values
satisfy `predecessorLayerStepFormulaAt`, and whose value at `index` is
`output`.  There is no reference to the ambient recursive function in the
formula. -/
def predecessorLayerHistoryFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2)) : FOFormula (n + 3) :=
  let params : Fin n -> Fin (n + 3) :=
    fun i => i.castSucc.castSucc.castSucc
  let top : Fin (n + 3) := (Fin.last n).castSucc.castSucc
  let index : Fin (n + 3) := (Fin.last (n + 1)).castSucc
  let output : Fin (n + 3) := Fin.last (n + 2)
  .ex <| .conj
    (transitiveZFSuccessorAt
      (Fin.last (n + 3)) index.castSucc)
    (.ex <| .conj
      (functionGraphOnFormulaAt
        (Fin.last (n + 4)) (Fin.last (n + 3)).castSucc)
      (.conj
        (graphValueFormulaAt
          (Fin.last (n + 4)) index.castSucc.castSucc
          output.castSucc.castSucc)
        (.conj
          (.ex <| .conj
            (transitiveZFEmptyAt (Fin.last (n + 5)))
            (.ex <| .conj
              (graphValueFormulaAt
                (Fin.last (n + 4)).castSucc.castSucc
                (Fin.last (n + 5)).castSucc (Fin.last (n + 6)))
              (predecessorSetFormulaAt classFormula relationFormula
                (fun i => (params i).castSucc.castSucc.castSucc.castSucc)
                top.castSucc.castSucc.castSucc.castSucc
                (Fin.last (n + 6)))))
          (FOFormula.boundedAll index.castSucc.castSucc
            (predecessorHistoryStepFormulaAt classFormula relationFormula
              (fun i => (params i).castSucc.castSucc.castSucc)
              (Fin.last (n + 4)).castSucc (Fin.last (n + 5)))))))

/-- Raw restricted-model meaning of one predecessor-layer step. -/
def IsPredecessorLayerStepIn (M : Set ZFSet.{u}) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (current next : ZFSet.{u}) : Prop :=
  forall z : ZFSet.{u}, z ∈ M ->
    (z ∈ next <->
      exists y : ZFSet.{u}, y ∈ M ∧ y ∈ current ∧
        SatisfiesIn M classFormula (snoc params z) ∧
        SatisfiesIn M relationFormula (snoc (snoc params z) y))

/-- Raw restricted-model meaning of a complete finite predecessor history.
This is a semantic abbreviation, not an additional mathematical assumption. -/
def IsPredecessorLayerHistoryIn (M : Set ZFSet.{u}) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (top index output domain graph : ZFSet.{u}) :
    Prop :=
  domain = insert index index ∧
  ((forall input : ZFSet.{u}, input ∈ M -> input ∈ domain ->
      exists value : ZFSet.{u}, value ∈ M ∧
        ZFSet.pair input value ∈ graph ∧
        forall other : ZFSet.{u}, other ∈ M ->
          ZFSet.pair input other ∈ graph -> other = value) ∧
    forall pair : ZFSet.{u}, pair ∈ M -> pair ∈ graph ->
      exists input : ZFSet.{u}, input ∈ M ∧ input ∈ domain ∧
        exists value : ZFSet.{u}, value ∈ M ∧
          pair = ZFSet.pair input value) ∧
  ZFSet.pair index output ∈ graph ∧
  (exists zero : ZFSet.{u}, zero ∈ M ∧ zero = (∅ : ZFSet.{u}) ∧
    exists base : ZFSet.{u}, base ∈ M ∧
      ZFSet.pair zero base ∈ graph ∧
      forall z : ZFSet.{u}, z ∈ M ->
        (z ∈ base <->
          SatisfiesIn M classFormula (snoc params z) ∧
          SatisfiesIn M relationFormula (snoc (snoc params z) top))) ∧
  forall i : ZFSet.{u}, i ∈ M -> i ∈ index ->
    exists successor : ZFSet.{u}, successor ∈ M ∧
      successor = insert i i ∧
      exists current : ZFSet.{u}, current ∈ M ∧
        ZFSet.pair i current ∈ graph ∧
        exists next : ZFSet.{u}, next ∈ M ∧
          ZFSet.pair successor next ∈ graph ∧
          IsPredecessorLayerStepIn M classFormula relationFormula
            params current next

private theorem internalPC_snoc_mem
    {M : Set ZFSet.{u}} {m : Nat} {s : Tuple ZFSet.{u} m}
    (hs : forall i, s i ∈ M) {x : ZFSet.{u}} (hx : x ∈ M) :
    forall i, snoc s x i ∈ M := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hx
  · simpa using hs j

/-- Exact restricted-satisfaction semantics of
`predecessorLayerHistoryFormula`. -/
@[simp]
theorem satisfiesIn_predecessorLayerHistoryFormula_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (top index output : ZFSet.{u})
    (hparams : forall i, params i ∈ M)
    (htop : top ∈ M) (hindex : index ∈ M) (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (predecessorLayerHistoryFormula classFormula relationFormula)
        (snoc (snoc (snoc params top) index) output) <->
      exists domain : ZFSet.{u}, domain ∈ (M : Set ZFSet.{u}) ∧
        exists graph : ZFSet.{u}, graph ∈ (M : Set ZFSet.{u}) ∧
          IsPredecessorLayerHistoryIn (M : Set ZFSet.{u})
            classFormula relationFormula params top index output domain graph := by
  let s : Tuple ZFSet.{u} (n + 3) :=
    snoc (snoc (snoc params top) index) output
  have hs : forall i, s i ∈ (M : Set ZFSet.{u}) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [s] using houtput
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa [s] using hindex
      · refine Fin.lastCases ?_ (fun l => ?_) k
        · simpa [s] using htop
        · simpa [s] using hparams l
  change SatisfiesIn (M : Set ZFSet.{u})
      (predecessorLayerHistoryFormula classFormula relationFormula) s <-> _
  rw [predecessorLayerHistoryFormula]
  simp only [SatisfiesIn]
  constructor
  · rintro ⟨domain, hdomainM, hdomainFormula,
      graph, hgraphM, hfunctionFormula, houtputFormula,
      hbaseFormula, hstepsFormula⟩
    have hsDomain := internalPC_snoc_mem hs hdomainM
    have hsGraph := internalPC_snoc_mem hsDomain hgraphM
    have hdomain :=
      (satisfiesIn_transitiveZFSuccessorAt_iff hM
        (Fin.last (n + 3)) (Fin.last (n + 1)).castSucc.castSucc
        (snoc s domain) hsDomain).mp hdomainFormula
    have hfunction :=
      (satisfiesIn_functionGraphOnFormulaAt_iff hM
        (Fin.last (n + 4)) (Fin.last (n + 3)).castSucc
        (snoc (snoc s domain) graph) hsGraph).mp hfunctionFormula
    have houtputGraph :=
      (satisfiesIn_graphValueFormulaAt_iff hM
        (Fin.last (n + 4))
        (Fin.last (n + 1)).castSucc.castSucc.castSucc
        (Fin.last (n + 2)).castSucc.castSucc
        (snoc (snoc s domain) graph) hsGraph).mp houtputFormula
    rcases hbaseFormula with
      ⟨zero, hzeroM, hzeroFormula, base, hbaseM,
        hbaseGraphFormula, hbaseSetFormula⟩
    have hsZero := internalPC_snoc_mem hsGraph hzeroM
    have hsBase := internalPC_snoc_mem hsZero hbaseM
    have hzero :=
      (satisfiesIn_transitiveZFEmptyAt_iff hM
        (Fin.last (n + 5)) (snoc (snoc (snoc s domain) graph) zero)
        hsZero).mp hzeroFormula
    have hbaseGraph :=
      (satisfiesIn_graphValueFormulaAt_iff hM
        (Fin.last (n + 4)).castSucc.castSucc
        (Fin.last (n + 5)).castSucc (Fin.last (n + 6))
        (snoc (snoc (snoc (snoc s domain) graph) zero) base)
        hsBase).mp hbaseGraphFormula
    have hbaseSet :=
      (satisfiesIn_predecessorSetFormulaAt_iff
        (M : Set ZFSet.{u}) classFormula relationFormula
        (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
        (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
        (Fin.last (n + 6))
        (snoc (snoc (snoc (snoc s domain) graph) zero) base)).mp
          hbaseSetFormula
    have hsteps :=
      (internalPC_satisfiesIn_boundedAll_iff
        (M : Set ZFSet.{u})
        (Fin.last (n + 1)).castSucc.castSucc.castSucc
        (predecessorHistoryStepFormulaAt classFormula relationFormula
          (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 4)).castSucc (Fin.last (n + 5)))
        (snoc (snoc s domain) graph)).mp hstepsFormula
    refine ⟨domain, hdomainM, graph, hgraphM, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [s, snoc_last, snoc_castSucc] using hdomain
    · simpa [s] using hfunction
    · simpa only [s, snoc_last, snoc_castSucc] using houtputGraph
    · refine ⟨zero, hzeroM, ?_, base, hbaseM, ?_, ?_⟩
      · simpa only [snoc_last, snoc_castSucc] using hzero
      · simpa only [snoc_last, snoc_castSucc] using hbaseGraph
      · simpa only [s, snoc_last, snoc_castSucc] using hbaseSet
    · intro i hiM hiIndex
      have hstepFormula := hsteps i hiM (by
        simpa only [s, snoc_last, snoc_castSucc] using hiIndex)
      have hsIndex := internalPC_snoc_mem hsGraph hiM
      have hstep :=
        (satisfiesIn_predecessorHistoryStepFormulaAt_iff hM
          classFormula relationFormula
          (fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 4)).castSucc (Fin.last (n + 5))
          (snoc (snoc (snoc s domain) graph) i) hsIndex).mp
            hstepFormula
      simpa only [IsPredecessorLayerStepIn, s,
        snoc_last, snoc_castSucc] using hstep
  · rintro ⟨domain, hdomainM, graph, hgraphM,
      hdomain, hfunction, houtputGraph, hbase, hsteps⟩
    have hsDomain := internalPC_snoc_mem hs hdomainM
    have hsGraph := internalPC_snoc_mem hsDomain hgraphM
    refine ⟨domain, hdomainM, ?_, graph, hgraphM, ?_, ?_, ?_, ?_⟩
    · apply (satisfiesIn_transitiveZFSuccessorAt_iff hM
        (Fin.last (n + 3)) (Fin.last (n + 1)).castSucc.castSucc
        (snoc s domain) hsDomain).mpr
      simpa only [s, snoc_last, snoc_castSucc] using hdomain
    · apply (satisfiesIn_functionGraphOnFormulaAt_iff hM
        (Fin.last (n + 4)) (Fin.last (n + 3)).castSucc
        (snoc (snoc s domain) graph) hsGraph).mpr
      simpa [s] using hfunction
    · apply (satisfiesIn_graphValueFormulaAt_iff hM
        (Fin.last (n + 4))
        (Fin.last (n + 1)).castSucc.castSucc.castSucc
        (Fin.last (n + 2)).castSucc.castSucc
        (snoc (snoc s domain) graph) hsGraph).mpr
      simpa only [s, snoc_last, snoc_castSucc] using houtputGraph
    · rcases hbase with
        ⟨zero, hzeroM, hzero, base, hbaseM, hbaseGraph, hbaseSet⟩
      have hsZero := internalPC_snoc_mem hsGraph hzeroM
      have hsBase := internalPC_snoc_mem hsZero hbaseM
      refine ⟨zero, hzeroM, ?_, base, hbaseM, ?_, ?_⟩
      · apply (satisfiesIn_transitiveZFEmptyAt_iff hM
          (Fin.last (n + 5))
          (snoc (snoc (snoc s domain) graph) zero) hsZero).mpr
        simpa only [snoc_last, snoc_castSucc] using hzero
      · apply (satisfiesIn_graphValueFormulaAt_iff hM
          (Fin.last (n + 4)).castSucc.castSucc
          (Fin.last (n + 5)).castSucc (Fin.last (n + 6))
          (snoc (snoc (snoc (snoc s domain) graph) zero) base)
          hsBase).mpr
        simpa only [snoc_last, snoc_castSucc] using hbaseGraph
      · apply (satisfiesIn_predecessorSetFormulaAt_iff
          (M : Set ZFSet.{u}) classFormula relationFormula
          (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
          (Fin.last (n + 6))
          (snoc (snoc (snoc (snoc s domain) graph) zero) base)).mpr
        simpa only [s, snoc_last, snoc_castSucc] using hbaseSet
    · apply (internalPC_satisfiesIn_boundedAll_iff
        (M : Set ZFSet.{u})
        (Fin.last (n + 1)).castSucc.castSucc.castSucc
        (predecessorHistoryStepFormulaAt classFormula relationFormula
          (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 4)).castSucc (Fin.last (n + 5)))
        (snoc (snoc s domain) graph)).mpr
      intro i hiM hiIndex
      have hsIndex := internalPC_snoc_mem hsGraph hiM
      apply (satisfiesIn_predecessorHistoryStepFormulaAt_iff hM
        classFormula relationFormula
        (fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
        (Fin.last (n + 4)).castSucc (Fin.last (n + 5))
        (snoc (snoc (snoc s domain) graph) i) hsIndex).mpr
      have hstep := hsteps i hiM (by
        simpa only [s, snoc_last, snoc_castSucc] using hiIndex)
      simpa only [IsPredecessorLayerStepIn, s,
        snoc_last, snoc_castSucc] using hstep

/-! ## Uniqueness of finite histories -/

/-- Restricted predecessor-set semantics identifies an internal candidate
with the ambient displayed predecessor set. -/
theorem eq_displayedPredecessors_of_restricted_semantics
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hsetLike : HasSetPredecessorsOn A R)
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    {x predecessors : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A)
    (hpredecessorsM : predecessors ∈ M)
    (hpredecessors : forall z : ZFSet.{u}, z ∈ (M : Set ZFSet.{u}) ->
      (z ∈ predecessors <->
        SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) ∧
        SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params z) x))) :
    predecessors = displayedPredecessors A R hsetLike x := by
  apply eq_displayedPredecessors_of_isPredecessorSet hsetLike hxA
  intro z
  constructor
  · intro hz
    have hzM : z ∈ M := hM.mem_trans hz hpredecessorsM
    have hzSemantic := (hpredecessors z hzM).mp hz
    exact ⟨(hclass z hzM).mp hzSemantic.1,
      (hrelationFormula z hzM x hxM).mp hzSemantic.2⟩
  · rintro ⟨hzA, hzx⟩
    have hzM : z ∈ M := hclosedIn x hxM z hzA hzx
    exact (hpredecessors z hzM).mpr
      ⟨(hclass z hzM).mpr hzA,
        (hrelationFormula z hzM x hxM).mpr hzx⟩

/-- A restricted semantic successor step from the actual `k`-th layer has
exactly the actual `(k+1)`-st layer as output. -/
theorem eq_predecessorLayer_succ_of_step
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hsetLike : HasSetPredecessorsOn A R)
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    {x next : ZFSet.{u}} (hxA : x ∈ A) (k : Nat)
    (hLayerM : predecessorLayer A R hsetLike x k ∈ M)
    (hnextM : next ∈ M)
    (hstep : IsPredecessorLayerStepIn (M : Set ZFSet.{u})
      classFormula relationFormula params
      (predecessorLayer A R hsetLike x k) next) :
    next = predecessorLayer A R hsetLike x (k + 1) := by
  apply ZFSet.ext
  intro z
  rw [mem_predecessorLayer_succ_iff hsetLike hxA k]
  constructor
  · intro hz
    have hzM : z ∈ M := hM.mem_trans hz hnextM
    rcases (hstep z hzM).mp hz with
      ⟨y, hyM, hyLayer, hzClass, hzyFormula⟩
    exact ⟨y, hyLayer, (hclass z hzM).mp hzClass,
      (hrelationFormula z hzM y hyM).mp hzyFormula⟩
  · rintro ⟨y, hyLayer, hzA, hzy⟩
    have hyM : y ∈ M := hM.mem_trans hyLayer hLayerM
    have hzM : z ∈ M := hclosedIn y hyM z hzA hzy
    exact (hstep z hzM).mpr
      ⟨y, hyM, hyLayer, (hclass z hzM).mpr hzA,
        (hrelationFormula z hzM y hyM).mpr hzy⟩

/-- The actual consecutive ambient layers satisfy the restricted semantic
step formula once both are known to be internal. -/
theorem isPredecessorLayerStepIn_predecessorLayer
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hsetLike : HasSetPredecessorsOn A R)
    {x : ZFSet.{u}} (hxA : x ∈ A) (k : Nat)
    (hLayerM : predecessorLayer A R hsetLike x k ∈ M) :
    IsPredecessorLayerStepIn (M : Set ZFSet.{u})
      classFormula relationFormula params
      (predecessorLayer A R hsetLike x k)
      (predecessorLayer A R hsetLike x (k + 1)) := by
  intro z hzM
  rw [mem_predecessorLayer_succ_iff hsetLike hxA k]
  constructor
  · rintro ⟨y, hyLayer, hzA, hzy⟩
    have hyM : y ∈ M := hM.mem_trans hyLayer hLayerM
    exact ⟨y, hyM, hyLayer, (hclass z hzM).mpr hzA,
      (hrelationFormula z hzM y hyM).mpr hzy⟩
  · rintro ⟨y, hyM, hyLayer, hzClass, hzyFormula⟩
    exact ⟨y, hyLayer, (hclass z hzM).mp hzClass,
      (hrelationFormula z hzM y hyM).mp hzyFormula⟩

/-- Every semantic finite history has the canonical output `p_k(x)`.

The induction uses only the single-valuedness of the quantified finite graph
and the two semantic identification lemmas above. -/
theorem output_eq_predecessorLayer_of_history
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hsetLike : HasSetPredecessorsOn A R)
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    {x output domain graph : ZFSet.{u}}
    (hxM : x ∈ M) (hxA : x ∈ A) (houtputM : output ∈ M)
    (hlayers : forall j : Nat,
      predecessorLayer A R hsetLike x j ∈ M)
    (k : Nat)
    (hhistory : IsPredecessorLayerHistoryIn (M : Set ZFSet.{u})
      classFormula relationFormula params x (natCode k) output domain graph) :
    output = predecessorLayer A R hsetLike x k := by
  rcases hhistory with
    ⟨hdomain, hfunction, houtputGraph, hbase, hsteps⟩
  have hindexM : forall j : Nat, natCode j ∈ M := by
    intro j
    simpa only [natCode] using natOrdinal_mem_of_isTransitiveZFModel hM j
  have hgraphAt : forall j : Nat, j ≤ k ->
      ZFSet.pair (natCode j) (predecessorLayer A R hsetLike x j) ∈ graph := by
    intro j hj
    induction j with
    | zero =>
        rcases hbase with
          ⟨zero, hzeroM, hzero, base, hbaseM, hbaseGraph, hbaseSet⟩
        have hbaseEq : base = displayedPredecessors A R hsetLike x :=
          eq_displayedPredecessors_of_restricted_semantics
            hM.1 classFormula relationFormula params hclass
            hrelationFormula hsetLike hclosedIn hxM hxA hbaseM hbaseSet
        simpa only [natCode, Nat.cast_zero, Ordinal.toZFSet_zero,
          predecessorLayer_zero, hzero, hbaseEq] using hbaseGraph
    | succ j ih =>
        have hjlt : j < k := Nat.lt_of_succ_le hj
        have hjle : j ≤ k := (Nat.le_succ j).trans hj
        have hindexIn : natCode j ∈ natCode k :=
          (IndexedSequenceZF.mem_natCode_iff_exists_lt
            (natCode j) k).mpr ⟨j, hjlt, rfl⟩
        rcases hsteps (natCode j) (hindexM j) hindexIn with
          ⟨successor, hsuccessorM, hsuccessor,
            current, hcurrentM, hcurrentGraph,
            next, hnextM, hnextGraph, hstep⟩
        have hcanonicalGraph := ih hjle
        have hdomainInput : natCode j ∈ domain := by
          rw [hdomain]
          rw [← FiniteSequenceZF.natCode_succ_eq_insert k]
          exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
            (natCode j) (k + 1)).mpr
              ⟨j, Nat.lt_succ_of_lt hjlt, rfl⟩
        rcases hfunction.1 (natCode j) (hindexM j) hdomainInput with
          ⟨value, hvalueM, hvalueGraph, hunique⟩
        have hcurrentEq : current =
            predecessorLayer A R hsetLike x j := by
          have hc := hunique current hcurrentM hcurrentGraph
          have hp := hunique (predecessorLayer A R hsetLike x j)
            (hlayers j) hcanonicalGraph
          exact hc.trans hp.symm
        subst current
        have hnextEq : next =
            predecessorLayer A R hsetLike x (j + 1) :=
          eq_predecessorLayer_succ_of_step hM.1 classFormula
            relationFormula params hclass hrelationFormula hsetLike
            hclosedIn hxA j (hlayers j) hnextM hstep
        rw [hsuccessor,
          ← FiniteSequenceZF.natCode_succ_eq_insert j,
          hnextEq] at hnextGraph
        simpa only [Nat.succ_eq_add_one] using hnextGraph
  have hcanonicalOutput := hgraphAt k le_rfl
  have hdomainK : natCode k ∈ domain := by
    rw [hdomain, ← FiniteSequenceZF.natCode_succ_eq_insert k]
    exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
      (natCode k) (k + 1)).mpr ⟨k, Nat.lt_succ_self k, rfl⟩
  rcases hfunction.1 (natCode k) (hindexM k) hdomainK with
    ⟨value, hvalueM, hvalueGraph, hunique⟩
  have houtputEq := hunique output houtputM houtputGraph
  have hcanonicalEq := hunique
    (predecessorLayer A R hsetLike x k) (hlayers k) hcanonicalOutput
  exact houtputEq.trans hcanonicalEq.symm

/-! ## Existence and exactness of canonical finite histories -/

/-- The canonical finite graph witnesses the semantic history assertion at
every standard natural number. -/
theorem exists_predecessorLayerHistoryIn
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hsetLike : HasSetPredecessorsOn A R)
    {x : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A)
    (hlayers : forall j : Nat,
      predecessorLayer A R hsetLike x j ∈ M) (k : Nat) :
    exists domain : ZFSet.{u}, domain ∈ M ∧
      exists graph : ZFSet.{u}, graph ∈ M ∧
        IsPredecessorLayerHistoryIn (M : Set ZFSet.{u})
          classFormula relationFormula params x (natCode k)
          (predecessorLayer A R hsetLike x k) domain graph := by
  let domain : ZFSet.{u} := natCode (k + 1)
  let graph : ZFSet.{u} :=
    predecessorLayerHistoryGraph A R hsetLike x k
  have hdomainM : domain ∈ M := by
    simpa only [domain, natCode] using
      natOrdinal_mem_of_isTransitiveZFModel hM (k + 1)
  have hgraphM : graph ∈ M := by
    exact predecessorLayerHistoryGraph_mem_of_layers
      hM hsetLike x hlayers k
  refine ⟨domain, hdomainM, graph, hgraphM, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact FiniteSequenceZF.natCode_succ_eq_insert k
  · exact predecessorLayerHistoryGraph_isFunctionGraph
      hM hsetLike x hlayers k
  · exact (mem_predecessorLayerHistoryGraph_iff
      hsetLike x k _).mpr ⟨k, le_rfl, rfl⟩
  · refine ⟨(∅ : ZFSet.{u}),
      empty_mem_of_isTransitiveZFModel hM, rfl,
      predecessorLayer A R hsetLike x 0, hlayers 0, ?_, ?_⟩
    · simpa only [natCode, Nat.cast_zero, Ordinal.toZFSet_zero] using
        (mem_predecessorLayerHistoryGraph_iff
          hsetLike x k (ZFSet.pair (natCode 0)
            (predecessorLayer A R hsetLike x 0))).mpr
          ⟨0, Nat.zero_le k, rfl⟩
    · intro z hzM
      rw [predecessorLayer_zero,
        displayedPredecessors_spec hsetLike hxA z]
      exact and_congr (hclass z hzM).symm
        (hrelationFormula z hzM x hxM).symm
  · intro i hiM hiIndex
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt i k).mp hiIndex with
      ⟨j, hj, rfl⟩
    refine ⟨natCode (j + 1), ?_,
      FiniteSequenceZF.natCode_succ_eq_insert j,
      predecessorLayer A R hsetLike x j, hlayers j, ?_,
      predecessorLayer A R hsetLike x (j + 1), hlayers (j + 1), ?_, ?_⟩
    · simpa [natCode] using
        natOrdinal_mem_of_isTransitiveZFModel hM (j + 1)
    · exact (mem_predecessorLayerHistoryGraph_iff
        hsetLike x k _).mpr ⟨j, Nat.le_of_lt hj, rfl⟩
    · exact (mem_predecessorLayerHistoryGraph_iff
        hsetLike x k _).mpr ⟨j + 1, hj, rfl⟩
    · exact isPredecessorLayerStepIn_predecessorLayer
        hM.1 classFormula relationFormula params hclass hrelationFormula
        hsetLike hxA j (hlayers j)

/-- The uniform history formula defines exactly the ambient `k`-th
predecessor layer over the transitive model. -/
theorem satisfiesIn_predecessorLayerHistoryFormula_natCode_iff
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hsetLike : HasSetPredecessorsOn A R)
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    {x output : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A)
    (houtputM : output ∈ M)
    (hlayers : forall j : Nat,
      predecessorLayer A R hsetLike x j ∈ M) (k : Nat) :
    SatisfiesIn (M : Set ZFSet.{u})
        (predecessorLayerHistoryFormula classFormula relationFormula)
        (snoc (snoc (snoc params x) (natCode k)) output) <->
      output = predecessorLayer A R hsetLike x k := by
  have hindexM : natCode k ∈ M := by
    simpa only [natCode] using natOrdinal_mem_of_isTransitiveZFModel hM k
  rw [satisfiesIn_predecessorLayerHistoryFormula_iff
    hM.1 classFormula relationFormula params x (natCode k) output
    hparams hxM hindexM houtputM]
  constructor
  · rintro ⟨domain, hdomainM, graph, hgraphM, hhistory⟩
    exact output_eq_predecessorLayer_of_history
      hM classFormula relationFormula params hclass hrelationFormula
      hsetLike hclosedIn hxM hxA houtputM hlayers k hhistory
  · intro houtput
    subst output
    exact exists_predecessorLayerHistoryIn
      hM classFormula relationFormula params hclass hrelationFormula
      hsetLike hxM hxA hlayers k

/-! ## Replacement over standard omega -/

/-- Replacement over the model-internal standard `omega`, followed by Union,
puts the ambient textbook predecessor closure into `M`.

The internal satisfaction of `setLikeRelationOnFormula` remains explicit: it
cannot be replaced by ambient set-likeness plus closure of predecessor
elements. -/
theorem predecessorClosure_mem_of_internal_setLike
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hsetLike : HasSetPredecessorsOn A R)
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {x : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A) :
    predecessorClosure A R hsetLike x ∈ M := by
  let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
  have homegaM : omega ∈ M := by
    exact omega_toZFSet_mem_of_isTransitiveZFModel hM
  let paramsM : Tuple (ZFCarrier M) n :=
    fun i => ⟨params i, hparams i⟩
  let xM : ZFCarrier M := ⟨x, hxM⟩
  let historyParamsM : Tuple (ZFCarrier M) (n + 1) :=
    Fin.snoc paramsM xM
  let omegaM : ZFCarrier M := ⟨omega, homegaM⟩
  have hhistoryParamsVal :
      zfCarrierTupleVal historyParamsM = snoc params x := by
    change zfCarrierTupleVal (Fin.snoc paramsM xM) = snoc params x
    rw [zfCarrierTupleVal_finSnoc]
    congr 1
  have hlayers : forall k : Nat,
      predecessorLayer A R hsetLike x k ∈ M :=
    predecessorLayer_mem_of_isTransitiveZFModel
      hM classFormula relationFormula params hparams hclass
      hrelationFormula hsetLike hclosedIn hsetLikeIn hxM hxA
  have hfun : forall index : ZFCarrier M, index.1 ∈ omegaM.1 ->
      ExistsUnique fun output : ZFCarrier M =>
        SatisfiesIn (M : Set ZFSet.{u})
          (predecessorLayerHistoryFormula classFormula relationFormula)
          (snoc (snoc (zfCarrierTupleVal historyParamsM) index.1)
            output.1) := by
    intro index hindexOmega
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindexOmega with ⟨k, hindex⟩
    let outputM : ZFCarrier M :=
      ⟨predecessorLayer A R hsetLike x k, hlayers k⟩
    refine ⟨outputM, ?_, ?_⟩
    · rw [hhistoryParamsVal, hindex]
      exact (satisfiesIn_predecessorLayerHistoryFormula_natCode_iff
        hM classFormula relationFormula params hparams hclass
        hrelationFormula hsetLike hclosedIn hxM hxA (hlayers k)
        hlayers k).mpr rfl
    · intro other hother
      apply Subtype.ext
      rw [hhistoryParamsVal, hindex] at hother
      exact (satisfiesIn_predecessorLayerHistoryFormula_natCode_iff
        hM classFormula relationFormula params hparams hclass
        hrelationFormula hsetLike hclosedIn hxM hxA other.2
        hlayers k).mp hother
  let range : ZFSet.{u} := M.sep fun output =>
    exists index : ZFSet.{u}, index ∈ omega ∧
      SatisfiesIn (M : Set ZFSet.{u})
        (predecessorLayerHistoryFormula classFormula relationFormula)
        (snoc (snoc (zfCarrierTupleVal historyParamsM) index) output)
  have hRangeM : range ∈ M := by
    exact satisfiesIn_replacementRange_mem_of_isTransitiveZFModel
      hM (predecessorLayerHistoryFormula classFormula relationFormula)
        historyParamsM omegaM hfun
  have hUnionM : ZFSet.sUnion range ∈ M :=
    sUnion_mem_of_isTransitiveZFModel hM hRangeM
  have hUnionEq : ZFSet.sUnion range =
      predecessorClosure A R hsetLike x := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sUnion, mem_predecessorClosure_iff]
    constructor
    · rintro ⟨layer, hlayerRange, hzLayer⟩
      rcases ZFSet.mem_sep.mp hlayerRange with
        ⟨hlayerM, index, hindexOmega, hhistory⟩
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index).mp
          hindexOmega with ⟨k, hindex⟩
      rw [hhistoryParamsVal, hindex] at hhistory
      have hlayerEq :=
        (satisfiesIn_predecessorLayerHistoryFormula_natCode_iff
          hM classFormula relationFormula params hparams hclass
          hrelationFormula hsetLike hclosedIn hxM hxA hlayerM
          hlayers k).mp hhistory
      exact ⟨k, by simpa only [hlayerEq] using hzLayer⟩
    · rintro ⟨k, hzLayer⟩
      refine ⟨predecessorLayer A R hsetLike x k, ?_, hzLayer⟩
      apply ZFSet.mem_sep.mpr
      refine ⟨hlayers k, natCode k, ?_, ?_⟩
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode k)).mpr ⟨k, rfl⟩
      · rw [hhistoryParamsVal]
        exact (satisfiesIn_predecessorLayerHistoryFormula_natCode_iff
          hM classFormula relationFormula params hparams hclass
          hrelationFormula hsetLike hclosedIn hxM hxA (hlayers k)
          hlayers k).mpr rfl
  simpa only [← hUnionEq] using hUnionM

/-- Textbook-facing wrapper retaining the full well-founded set-like
relation hypothesis. -/
theorem predecessorClosure_mem_of_isTransitiveZFModel
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hR : IsWellFoundedSetLikeOn A R)
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {x : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A) :
    predecessorClosure A R hR.2.2 x ∈ M :=
  predecessorClosure_mem_of_internal_setLike
    hM classFormula relationFormula params hparams hclass
      hrelationFormula hR.2.2 hclosedIn hsetLikeIn hxM hxA

/-- The actual textbook local domain `d_x = {x} ∪ cl(A,x,R)` belongs to
the transitive model.  No separate `hlocalM` assumption remains. -/
theorem localRecursionDomain_mem_of_isTransitiveZFModel
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hR : IsWellFoundedSetLikeOn A R)
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {x : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A) :
    localRecursionDomain A R hR.2.2 x ∈ M := by
  have hclosureM : predecessorClosure A R hR.2.2 x ∈ M :=
    predecessorClosure_mem_of_isTransitiveZFModel
      hM classFormula relationFormula params hparams hclass
      hrelationFormula hR hclosedIn hsetLikeIn hxM hxA
  rw [localRecursionDomain, ← ZFSet.insert_eq]
  exact insert_mem_of_isTransitiveZFModel hM hxM hclosureM

end

end Constructible.Model
