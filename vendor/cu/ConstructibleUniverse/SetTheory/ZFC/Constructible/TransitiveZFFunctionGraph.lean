/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0Godel
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.RestrictionGraph
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFReplacement

/-!
# Internally represented function graphs in transitive ZF set models

Given a formula `phi(params, x, y)` that has one unique model-internal value
for each `x` in an internal domain, this file constructs the actual internal
Kuratowski graph

`{ <x,y> | x in a and M satisfies phi(params,x,y) }`.

The graph is obtained by applying the model's Replacement scheme to the
object-language formula

`exists y, phi(params,x,y) and q = <x,y>`.

Thus neither an external Lean function nor `ZFSet.range` is used as a
substitute for the internally represented graph.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-! ## The object-language graph-output formula -/

/-- Rename `(params,x,y)` into `(params,x,q,y)`. -/
def replacementGraphPredicateRename {n : Nat} :
    Fin (n + 2) -> Fin (n + 3) :=
  Fin.lastCases
    (Fin.last (n + 2))
    (fun j => Fin.lastCases
      (Fin.castSucc (Fin.castSucc (Fin.last n)))
      (fun i => i.castSucc.castSucc.castSucc)
      j)

/-- The renaming has the intended effect after introducing the value
witness `y`. -/
theorem comp_replacementGraphPredicateRename {A : Type u} {n : Nat}
    (params : Tuple A n) (x q y : A) :
    (fun i => snoc (snoc (snoc params x) q) y
      (replacementGraphPredicateRename i)) =
      snoc (snoc params x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [replacementGraphPredicateRename]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [replacementGraphPredicateRename]
    · simp [replacementGraphPredicateRename]

/-- The input coordinate in `(params,x,q,y)`. -/
def replacementGraphInputIndex (n : Nat) : Fin (n + 3) :=
  (Fin.last n).castSucc.castSucc

/-- The prospective pair coordinate in `(params,x,q,y)`. -/
def replacementGraphPairIndex (n : Nat) : Fin (n + 3) :=
  (Fin.last (n + 1)).castSucc

/-- The value witness coordinate in `(params,x,q,y)`. -/
def replacementGraphValueIndex (n : Nat) : Fin (n + 3) :=
  Fin.last (n + 2)

/-- `replacementGraphFormula phi(params,x,q)` says that `q` is the
Kuratowski pair of `x` with the unique value selected by `phi`. -/
def replacementGraphFormula {n : Nat} (phi : FOFormula (n + 2)) :
    FOFormula (n + 2) :=
  .ex (.conj
    (FOFormula.rename replacementGraphPredicateRename phi)
    (Delta0Formula.kuratowskiPairEqAt
      (replacementGraphPairIndex n)
      (replacementGraphInputIndex n)
      (replacementGraphValueIndex n)).toFO)

/-- Kuratowski-pair equality is absolute to a transitive carrier. -/
theorem satisfies_kuratowskiPairEqAt_zfCarrier
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (pair x y : Fin n) (s : Tuple (ZFCarrier M) n) :
    FOFormula.Satisfies (zfCarrierMem M)
        (Delta0Formula.kuratowskiPairEqAt pair x y).toFO s <->
      (s pair).1 = ZFSet.pair (s x).1 (s y).1 := by
  rw [Delta0Formula.satisfies_toFO_absolute hM,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  simp only [Delta0Formula.val_apply]

/-- Exact carrier semantics of the formula that outputs graph pairs. -/
theorem satisfies_replacementGraphFormula
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple (ZFCarrier M) n) (x q : ZFCarrier M) :
    FOFormula.Satisfies (zfCarrierMem M)
        (replacementGraphFormula phi) (snoc (snoc params x) q) <->
      exists y : ZFCarrier M,
        FOFormula.Satisfies (zfCarrierMem M) phi
          (snoc (snoc params x) y) ∧
        q.1 = ZFSet.pair x.1 y.1 := by
  simp only [replacementGraphFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename,
    satisfies_kuratowskiPairEqAt_zfCarrier hM,
    comp_replacementGraphPredicateRename,
    replacementGraphPairIndex, replacementGraphInputIndex,
    replacementGraphValueIndex, snoc_last, snoc_castSucc]

/-- Raw restricted semantics of the formula that outputs graph pairs. -/
theorem satisfiesIn_replacementGraphFormula
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple (ZFCarrier M) n) (x q : ZFCarrier M) :
    SatisfiesIn (M : Set ZFSet.{u}) (replacementGraphFormula phi)
        (snoc (snoc (zfCarrierTupleVal params) x.1) q.1) <->
      exists y : ZFCarrier M,
        SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (snoc (zfCarrierTupleVal params) x.1) y.1) ∧
        q.1 = ZFSet.pair x.1 y.1 := by
  have hgraph :
      FOFormula.Satisfies (zfCarrierMem M)
          (replacementGraphFormula phi) (snoc (snoc params x) q) <->
        SatisfiesIn (M : Set ZFSet.{u}) (replacementGraphFormula phi)
          (snoc (snoc (zfCarrierTupleVal params) x.1) q.1) := by
    have h := satisfies_zfCarrier_iff_satisfiesIn M
      (replacementGraphFormula phi) (snoc (snoc params x) q)
    rw [subtypeVal_snoc, subtypeVal_snoc] at h
    exact h
  have hphi (y : ZFCarrier M) :
      FOFormula.Satisfies (zfCarrierMem M) phi
          (snoc (snoc params x) y) <->
        SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (snoc (zfCarrierTupleVal params) x.1) y.1) := by
    have h := satisfies_zfCarrier_iff_satisfiesIn M phi
      (snoc (snoc params x) y)
    rw [subtypeVal_snoc, subtypeVal_snoc] at h
    exact h
  constructor
  · intro h
    rcases (satisfies_replacementGraphFormula hM phi params x q).mp
        (hgraph.mpr h) with ⟨y, hy, hq⟩
    refine ⟨y, ?_, hq⟩
    exact (hphi y).mp hy
  · rintro ⟨y, hy, hq⟩
    apply hgraph.mp
    apply (satisfies_replacementGraphFormula hM phi params x q).mpr
    refine ⟨y, ?_, hq⟩
    exact (hphi y).mpr hy

/-! ## Internal graph existence -/

/-- A formula-functional relation on an internal set has an actual
Kuratowski function graph belonging to the model. -/
theorem exists_zfCarrier_satisfiesIn_functionGraph
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple (ZFCarrier M) n) (a : ZFCarrier M)
    (hfun : forall x : ZFCarrier M, x.1 ∈ a.1 ->
      ExistsUnique fun y : ZFCarrier M =>
        SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (snoc (zfCarrierTupleVal params) x.1) y.1)) :
    Exists fun graph : ZFCarrier M => forall q : ZFSet.{u},
      q ∈ graph.1 <->
        exists x : ZFSet.{u}, x ∈ a.1 ∧
          exists y : ZFSet.{u}, y ∈ M ∧
            SatisfiesIn (M : Set ZFSet.{u}) phi
              (snoc (snoc (zfCarrierTupleVal params) x) y) ∧
            q = ZFSet.pair x y := by
  have hGraphFun : forall x : ZFCarrier M, x.1 ∈ a.1 ->
      ExistsUnique fun q : ZFCarrier M =>
        SatisfiesIn (M : Set ZFSet.{u})
          (replacementGraphFormula phi)
          (snoc (snoc (zfCarrierTupleVal params) x.1) q.1) := by
    intro x hx
    rcases hfun x hx with ⟨y, hy, hyUnique⟩
    have hpairM : ZFSet.pair x.1 y.1 ∈ M :=
      kuratowskiPair_mem_of_isTransitiveZFModel hM x.2 y.2
    let q : ZFCarrier M := ⟨ZFSet.pair x.1 y.1, hpairM⟩
    refine ⟨q, ?_, ?_⟩
    · apply (satisfiesIn_replacementGraphFormula hM.1 phi params x q).mpr
      exact ⟨y, hy, rfl⟩
    · intro q' hq'
      rcases (satisfiesIn_replacementGraphFormula hM.1
          phi params x q').mp hq' with ⟨y', hy', hq'⟩
      have hyy' : y' = y := hyUnique y' hy'
      apply Subtype.ext
      rw [hq', hyy']
  rcases exists_zfCarrier_satisfiesIn_replacementRange hM
      (replacementGraphFormula phi) params a hGraphFun with ⟨graph, hgraph⟩
  refine ⟨graph, ?_⟩
  intro q
  constructor
  · intro hq
    rcases (hgraph q).mp hq with ⟨hqM, x, hxa, hformula⟩
    have hxM : x ∈ M := hM.1.mem_trans hxa a.2
    let xM : ZFCarrier M := ⟨x, hxM⟩
    let qM : ZFCarrier M := ⟨q, hqM⟩
    rcases (satisfiesIn_replacementGraphFormula hM.1
        phi params xM qM).mp hformula with ⟨y, hy, hqPair⟩
    exact ⟨x, hxa, y.1, y.2, hy, hqPair⟩
  · rintro ⟨x, hxa, y, hyM, hphi, hqPair⟩
    have hxM : x ∈ M := hM.1.mem_trans hxa a.2
    have hpairM : ZFSet.pair x y ∈ M :=
      kuratowskiPair_mem_of_isTransitiveZFModel hM hxM hyM
    have hqM : q ∈ M := by simpa only [hqPair] using hpairM
    let xM : ZFCarrier M := ⟨x, hxM⟩
    let qM : ZFCarrier M := ⟨q, hqM⟩
    apply (hgraph q).mpr
    refine ⟨hqM, x, hxa, ?_⟩
    apply (satisfiesIn_replacementGraphFormula hM.1
      phi params xM qM).mpr
    let yM : ZFCarrier M := ⟨y, hyM⟩
    refine ⟨yM, hphi, ?_⟩
    exact hqPair

/-! ## Identification with an ambient function restriction -/

/-- If `phi` defines an ambient function `F` correctly in the model and `F`
is closed on the internal domain `a`, the model's Replacement witness is
exactly the actual restriction graph of `F` to `a`. -/
theorem exists_zfCarrier_eq_predecessorRestrictionGraph_of_formula
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple (ZFCarrier M) n) (a : ZFCarrier M)
    (F : ZFSet.{u} -> ZFSet.{u})
    (hclosed : forall x, x ∈ a.1 -> F x ∈ M)
    (hgraph : forall x, x ∈ a.1 -> forall y, y ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) phi
        (snoc (snoc (zfCarrierTupleVal params) x) y) <->
        y = F x)) :
    Exists fun graph : ZFCarrier M =>
      graph.1 = predecessorRestrictionGraph a.1 F := by
  have hfun : forall x : ZFCarrier M, x.1 ∈ a.1 ->
      ExistsUnique fun y : ZFCarrier M =>
        SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (snoc (zfCarrierTupleVal params) x.1) y.1) := by
    intro x hx
    have hFxM : F x.1 ∈ M := hclosed x.1 hx
    let y : ZFCarrier M := ⟨F x.1, hFxM⟩
    refine ⟨y, ?_, ?_⟩
    · exact (hgraph x.1 hx y.1 y.2).mpr rfl
    · intro z hz
      apply Subtype.ext
      exact (hgraph x.1 hx z.1 z.2).mp hz
  rcases exists_zfCarrier_satisfiesIn_functionGraph
      hM phi params a hfun with ⟨graph, hgraphMem⟩
  refine ⟨graph, ?_⟩
  apply ZFSet.ext
  intro q
  constructor
  · intro hq
    rcases (hgraphMem q).mp hq with
      ⟨x, hx, y, hyM, hphi, hqPair⟩
    have hyF : y = F x := (hgraph x hx y hyM).mp hphi
    apply mem_predecessorRestrictionGraph_iff.mpr
    refine ⟨x, hx, ?_⟩
    exact (congrArg (ZFSet.pair x) hyF).symm.trans hqPair.symm
  · intro hq
    rcases mem_predecessorRestrictionGraph_iff.mp hq with
      ⟨x, hx, hpair⟩
    have hFxM : F x ∈ M := hclosed x hx
    apply (hgraphMem q).mpr
    exact ⟨x, hx, F x, hFxM,
      (hgraph x hx (F x) hFxM).mpr rfl, hpair.symm⟩

/-- Under the same explicit closure and graph-correctness hypotheses, the
actual restriction graph belongs to the model. -/
theorem predecessorRestrictionGraph_mem_of_formula
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple (ZFCarrier M) n) (a : ZFCarrier M)
    (F : ZFSet.{u} -> ZFSet.{u})
    (hclosed : forall x, x ∈ a.1 -> F x ∈ M)
    (hgraph : forall x, x ∈ a.1 -> forall y, y ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) phi
        (snoc (snoc (zfCarrierTupleVal params) x) y) <->
        y = F x)) :
    predecessorRestrictionGraph a.1 F ∈ M := by
  rcases exists_zfCarrier_eq_predecessorRestrictionGraph_of_formula
      hM phi params a F hclosed hgraph with ⟨graph, hgraphEq⟩
  simpa only [← hgraphEq] using graph.2

/-! ## Packaging through `FunctionAbsoluteTo` -/

/-- The tuple presentation of a unary ambient domain. -/
def UnaryTupleDomain (A : Set ZFSet.{u}) :
    Set (Tuple ZFSet.{u} 1) :=
  {s | s 0 ∈ A}

/-- An absolute unary function has an internal restriction graph on every
internal set contained in its ambient domain. -/
theorem predecessorRestrictionGraph_mem_of_functionAbsoluteTo
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {A : Set ZFSet.{u}} (F : ZFSet.{u} -> ZFSet.{u})
    (phi : FOFormula 2)
    (habsolute : FunctionAbsoluteTo (M : Set ZFSet.{u})
      (UnaryTupleDomain A)
      (fun s : Tuple ZFSet.{u} 1 => F (s 0)) phi)
    (a : ZFCarrier M)
    (haA : forall x, x ∈ a.1 -> x ∈ A) :
    predecessorRestrictionGraph a.1 F ∈ M := by
  let params : Tuple (ZFCarrier M) 0 := fun i => Fin.elim0 i
  apply predecessorRestrictionGraph_mem_of_formula
    hM phi params a F
  · intro x hx
    have hxM : x ∈ M := hM.1.mem_trans hx a.2
    let s : Tuple ZFSet.{u} 1 := ![x]
    have hsM : TupleIn (M : Set ZFSet.{u}) s := by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change x ∈ M
      exact hxM
    have hsA : s ∈ UnaryTupleDomain A := by
      change x ∈ A
      exact haA x hx
    have hclosed := habsolute.1 s hsM hsA
    change F x ∈ M at hclosed
    exact hclosed
  · intro x hx y hyM
    have hxM : x ∈ M := hM.1.mem_trans hx a.2
    let s : Tuple ZFSet.{u} 1 := ![x]
    have hsM : TupleIn (M : Set ZFSet.{u}) s := by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change x ∈ M
      exact hxM
    have hsA : s ∈ UnaryTupleDomain A := by
      change x ∈ A
      exact haA x hx
    have hassignment :
        snoc (snoc (zfCarrierTupleVal params) x) y = snoc s y := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · have hj : j = 0 := Subsingleton.elim _ _
        subst j
        change x = x
        rfl
    rw [hassignment]
    have hgraph := habsolute.2 s y hsM hyM
    constructor
    · intro hphi
      have hyF := (hgraph.mp hphi).2
      change y = F x at hyF
      exact hyF
    · intro hyF
      have hyF' : y = F (s 0) := by
        change y = F x
        exact hyF
      exact hgraph.mpr ⟨hsA, hyF'⟩

end

end Constructible.Model
