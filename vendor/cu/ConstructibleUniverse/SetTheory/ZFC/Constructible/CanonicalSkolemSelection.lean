/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalDefinableRelationGraph
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.MinimalStage
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Replacement
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryClosureConstructible
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryGraphSystem

/-!
# Canonical internal Skolem selection

This file isolates the set-sized choice operation needed by a Skolem-hull
construction.  A constructible graph internally well-orders a bounding set.
For a constructible family of nonempty subsets of that bound, one fixed
first-order formula selects the least member of each fiber.  Full Separation
then produces the actual Kuratowski-pair graph in `L`, and Replacement produces
its range.

The final section turns a relation in `rudimentaryClosure U` and a finite
parameter tuple into its witness set.  The witness set is explicitly
intersected with `U`: an arbitrary member of `rudimentaryClosure U` need not
contain only well-formed tuple codes.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## The fixed least-witness formula -/

/-- Under a new universally quantified variable, select `[order, z, y]` from
the context `[order, candidate, y, z]`. -/
def leastWitnessOrderRename : Fin 3 -> Fin 4 :=
  ![(0 : Fin 3).castSucc, Fin.last 3, (2 : Fin 3).castSucc]

private theorem comp_leastWitnessOrderRename {A : Type u}
    (order candidate y z : A) :
    (fun i => snoc ![order, candidate, y] z
      (leastWitnessOrderRename i)) =
      ![order, z, y] := by
  funext i
  fin_cases i <;> rfl

/-- With layout `[order, candidate, y]`, assert that `y` is the least member
of `candidate` in the relation represented by `order`. -/
def leastWitnessFormula : FOFormula 3 :=
  .conj
    (.mem (2 : Fin 3) (1 : Fin 3))
    (.all
      (FOFormula.imp
        (.mem (Fin.last 3) (1 : Fin 3).castSucc)
        (.neg (FOFormula.rename leastWitnessOrderRename graphRelFormula))))

@[simp]
theorem satisfies_leastWitnessFormula
    (order candidate y : LCarrier.{u}) :
    FOFormula.Satisfies LMem leastWitnessFormula ![order, candidate, y] <->
      y.1 ∈ candidate.1 /\
        forall z : LCarrier.{u}, z.1 ∈ candidate.1 ->
          Not (GraphRel order z y) := by
  simp only [leastWitnessFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_rename, satisfies_graphRelFormula]
  constructor
  · rintro ⟨hy, hminimal⟩
    refine ⟨hy, ?_⟩
    intro z hz
    have hrename := comp_leastWitnessOrderRename order candidate y z
    have h0 := congrFun hrename 0
    have h1 := congrFun hrename 1
    have h2 := congrFun hrename 2
    simpa [h0, h1, h2] using hminimal z hz
  · rintro ⟨hy, hminimal⟩
    refine ⟨hy, ?_⟩
    intro z hz
    have hrename := comp_leastWitnessOrderRename order candidate y z
    have h0 := congrFun hrename 0
    have h1 := congrFun hrename 1
    have h2 := congrFun hrename 2
    simpa [h0, h1, h2] using hminimal z hz

/-- Select `[order, x, y]` from `[family, order, x, y]`. -/
def leastWitnessFamilyRename : Fin 3 -> Fin 4 :=
  ![1, 2, 3]

private theorem comp_leastWitnessFamilyRename {A : Type u}
    (family order x y : A) :
    (fun i => ![family, order, x, y] (leastWitnessFamilyRename i)) =
      ![order, x, y] := by
  funext i
  fin_cases i <;> rfl

/-- Layout `[family, order, x, y]`: `x` is in the family and `y` is its
`order`-least member. -/
def leastWitnessFamilyFormula : FOFormula 4 :=
  .conj
    (.mem (2 : Fin 4) (0 : Fin 4))
    (FOFormula.rename leastWitnessFamilyRename leastWitnessFormula)

@[simp]
theorem satisfies_leastWitnessFamilyFormula
    (family order x y : LCarrier.{u}) :
    FOFormula.Satisfies LMem leastWitnessFamilyFormula
        ![family, order, x, y] <->
      x.1 ∈ family.1 /\ y.1 ∈ x.1 /\
        forall z : LCarrier.{u}, z.1 ∈ x.1 ->
          Not (GraphRel order z y) := by
  simp only [leastWitnessFamilyFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  rw [comp_leastWitnessFamilyRename,
    satisfies_leastWitnessFormula]
  change
    (x.1 ∈ family.1 /\ y.1 ∈ x.1 /\
      forall z : LCarrier.{u}, z.1 ∈ x.1 ->
        Not (GraphRel order z y)) <-> _
  rfl

private theorem leastWitnessFamily_assignment
    (family order x y : LCarrier.{u}) :
    snoc (snoc ![family, order] x) y = ![family, order, x, y] := by
  funext i
  fin_cases i <;> rfl

private theorem leastWitness_assignment
    (order x y : LCarrier.{u}) :
    snoc (snoc ![order] x) y = ![order, x, y] := by
  funext i
  fin_cases i <;> rfl

/-! ## A constructible choice graph for a set-sized family -/

/-- Every member of `family` is a subset of `stage`. -/
def FamilySubsets (family stage : LCarrier.{u}) : Prop :=
  forall x : LCarrier.{u}, x.1 ∈ family.1 ->
    forall z : LCarrier.{u}, z.1 ∈ x.1 -> z.1 ∈ stage.1

/-- The canonical Separation graph selecting the least member of each member
of `family`.  The union carrier contains both the input sets and their values. -/
def canonicalLeastChoiceGraph
    (family stage order : LCarrier.{u}) : LCarrier.{u} :=
  canonicalDefinableRelationGraph leastWitnessFamilyFormula
    ![family, order] (unionLCarrier family stage)

/-- Exact semantics of the internal choice graph. -/
theorem graphRel_canonicalLeastChoiceGraph_iff
    {family stage order : LCarrier.{u}}
    (hsub : FamilySubsets family stage)
    (x y : LCarrier.{u}) :
    GraphRel (canonicalLeastChoiceGraph family stage order) x y <->
      x.1 ∈ family.1 /\ y.1 ∈ x.1 /\
        forall z : LCarrier.{u}, z.1 ∈ x.1 ->
          Not (GraphRel order z y) := by
  rw [canonicalLeastChoiceGraph,
    graphRel_canonicalDefinableRelationGraph_iff]
  rw [leastWitnessFamily_assignment,
    satisfies_leastWitnessFamilyFormula]
  constructor
  · rintro ⟨_hxContainer, _hyContainer, hleast⟩
    exact hleast
  · rintro hleast
    refine ⟨?_, ?_, hleast⟩
    · exact (mem_unionLCarrier_iff family stage x).mpr
        (Or.inl hleast.1)
    · exact (mem_unionLCarrier_iff family stage y).mpr
        (Or.inr (hsub x hleast.1 y hleast.2.1))

/-- If `order` internally well-orders the bound and every fiber is nonempty,
the canonical graph has exactly one value at every member of the family. -/
theorem existsUnique_graphRel_canonicalLeastChoiceGraph
    {family stage order : LCarrier.{u}}
    (hwell : InternallyWellOrders order stage)
    (hsub : FamilySubsets family stage)
    (hnonempty : forall x : LCarrier.{u}, x.1 ∈ family.1 ->
      exists y : LCarrier.{u}, y.1 ∈ x.1)
    (x : LCarrier.{u}) (hx : x.1 ∈ family.1) :
    ∃! y : LCarrier.{u},
      GraphRel (canonicalLeastChoiceGraph family stage order) x y := by
  rcases exists_unique_graph_minimum hwell (hsub x hx)
      (hnonempty x hx) with ⟨y, hy, hunique⟩
  refine ⟨y, ?_, ?_⟩
  · exact (graphRel_canonicalLeastChoiceGraph_iff hsub x y).mpr
      ⟨hx, hy.1, hy.2⟩
  · intro y' hy'
    apply hunique y'
    have hleast :=
      (graphRel_canonicalLeastChoiceGraph_iff hsub x y').mp hy'
    exact ⟨hleast.2.1, hleast.2.2⟩

/-- Replacement collects the range of the canonical least-member operation
as another actual set in `L`. -/
theorem exists_canonicalLeastChoiceRange
    {family stage order : LCarrier.{u}}
    (hwell : InternallyWellOrders order stage)
    (hsub : FamilySubsets family stage)
    (hnonempty : forall x : LCarrier.{u}, x.1 ∈ family.1 ->
      exists y : LCarrier.{u}, y.1 ∈ x.1) :
    exists range : LCarrier.{u}, forall y : LCarrier.{u},
      y.1 ∈ range.1 <-> exists x : LCarrier.{u},
        x.1 ∈ family.1 /\
          GraphRel (canonicalLeastChoiceGraph family stage order) x y := by
  have hfun : forall x : LCarrier.{u}, x.1 ∈ family.1 ->
      ∃! y : LCarrier.{u},
        FOFormula.Satisfies LMem leastWitnessFormula ![order, x, y] := by
    intro x hx
    rcases exists_unique_graph_minimum hwell (hsub x hx)
        (hnonempty x hx) with ⟨y, hy, hunique⟩
    refine ⟨y, (satisfies_leastWitnessFormula order x y).mpr hy, ?_⟩
    intro y' hy'
    exact hunique y'
      ((satisfies_leastWitnessFormula order x y').mp hy')
  let params : Tuple LCarrier.{u} 1 := ![order]
  have hfun' : forall x : LCarrier.{u}, x.1 ∈ family.1 ->
      ∃! y : LCarrier.{u},
        FOFormula.Satisfies LMem leastWitnessFormula
          (snoc (snoc params x) y) := by
    intro x hx
    simpa only [params, leastWitness_assignment] using hfun x hx
  rcases exists_replacementLCarrier leastWitnessFormula params family hfun' with
    ⟨range, hrange⟩
  refine ⟨range, ?_⟩
  intro y
  rw [hrange]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  rw [show snoc (snoc params x) y = ![order, x, y] by
    funext i
    fin_cases i <;> rfl]
  rw [satisfies_leastWitnessFormula]
  constructor
  · intro hleast
    exact (graphRel_canonicalLeastChoiceGraph_iff hsub x y).mpr
      ⟨hx, hleast⟩
  · intro hgraph
    exact ((graphRel_canonicalLeastChoiceGraph_iff hsub x y).mp hgraph).2

/-! ## Witness sets attached to rudimentary relation codes -/

/-- A relation indexed by `rudimentaryClosure U`, repackaged as a member of
the membership structure on `L`. -/
def rudimentaryRelationLCarrier
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1)) : LCarrier.{u} :=
  ⟨relation.1, mem_L_of_mem relation.2
    (Godel.RudimentaryTerm.rudimentaryClosure_mem_L U)⟩

/-- The code of a nonempty tuple of members of `U`, packaged in `L`. -/
def positiveTupleCodeLCarrier
    (U : LCarrier.{u}) {n : Nat}
    (params : Tuple (ZFCarrier U.1) (n + 1)) : LCarrier.{u} :=
  ⟨Godel.positiveTupleCode n (Delta0Formula.val params),
    mem_L_of_mem (Godel.positiveTupleCode_mem_rudimentaryClosure params)
      (Godel.RudimentaryTerm.rudimentaryClosure_mem_L U)⟩

/-- Intersection, packaged as an element of `L`. -/
def restrictedLCarrier (x bound : LCarrier.{u}) : LCarrier.{u} :=
  ⟨x.1 ∩ bound.1, inter_mem_L x.2 bound.2⟩

@[simp]
theorem mem_restrictedLCarrier_iff
    (x bound z : LCarrier.{u}) :
    z.1 ∈ (restrictedLCarrier x bound).1 <->
      z.1 ∈ x.1 /\ z.1 ∈ bound.1 := by
  simp [restrictedLCarrier]

/-- Nullary relations use their members directly as witnesses, restricted to
the intended structure `U`. -/
def nullaryRudimentaryWitnessSet
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1)) : LCarrier.{u} :=
  restrictedLCarrier (rudimentaryRelationLCarrier U relation) U

/-- For a nonempty parameter tuple, witnesses form the appropriate fiber of
the represented relation, again restricted to `U`. -/
def positiveRudimentaryWitnessSet
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) (n + 1)) : LCarrier.{u} :=
  restrictedLCarrier
    ⟨Godel.fiber relation.1
        (Godel.positiveTupleCode n (Delta0Formula.val params)),
      Godel.fiber_mem_L (rudimentaryRelationLCarrier U relation).2
        (positiveTupleCodeLCarrier U params).2⟩
    U

@[simp]
theorem mem_nullaryRudimentaryWitnessSet_iff
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    (x : ZFCarrier U.1) :
    x.1 ∈ (nullaryRudimentaryWitnessSet U relation).1 <->
      x.1 ∈ relation.1 := by
  change x.1 ∈ relation.1 ∩ U.1 <-> x.1 ∈ relation.1
  rw [ZFSet.mem_inter]
  simp only [x.2, and_true]

@[simp]
theorem mem_positiveRudimentaryWitnessSet_iff
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) (n + 1))
    (x : ZFCarrier U.1) :
    x.1 ∈ (positiveRudimentaryWitnessSet U relation params).1 <->
      Godel.positiveTupleCode (n + 1)
        (Delta0Formula.val (snoc params x)) ∈ relation.1 := by
  change
    x.1 ∈ Godel.fiber relation.1
      (Godel.positiveTupleCode n (Delta0Formula.val params)) ∩ U.1 <-> _
  rw [ZFSet.mem_inter, Godel.mem_fiber_iff]
  simp only [Godel.positiveTupleCode_snoc, Delta0Formula.val_snoc,
    x.2, and_true]

/-- Witness candidates for an arbitrary finite parameter tuple. -/
def rudimentaryWitnessSet
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) n) : LCarrier.{u} :=
  match n, params with
  | 0, _ => nullaryRudimentaryWitnessSet U relation
  | _n + 1, params => positiveRudimentaryWitnessSet U relation params

@[simp]
theorem mem_rudimentaryWitnessSet_iff
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) n)
    (x : ZFCarrier U.1) :
    x.1 ∈ (rudimentaryWitnessSet U relation params).1 <->
      Godel.positiveTupleCode n
        (Delta0Formula.val (snoc params x)) ∈ relation.1 := by
  cases n with
  | zero =>
      have hparams : params = (fun i : Fin 0 => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      subst params
      change
        x.1 ∈ (nullaryRudimentaryWitnessSet U relation).1 <->
          x.1 ∈ relation.1
      exact mem_nullaryRudimentaryWitnessSet_iff U relation x
  | succ n =>
      simp [rudimentaryWitnessSet]

/-- Every selected witness candidate lies in the intended set-sized
structure, even when the rudimentary relation contains malformed codes. -/
theorem rudimentaryWitnessSet_subset
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) n) :
    (rudimentaryWitnessSet U relation params).1 ⊆ U.1 := by
  intro z hz
  cases n with
  | zero =>
      exact (ZFSet.mem_inter.mp hz).2
  | succ n =>
      exact (ZFSet.mem_inter.mp hz).2

/-! ## Specialization to the canonical stage order -/

/-- A canonical stage containing `U` and hence, by transitivity, every member
of `U`. -/
def canonicalWitnessStageOrdinal (U : LCarrier.{u}) : Ordinal.{u} :=
  Constructible.firstStage U.1 U.2

/-- The actual stage used to bound canonical witnesses. -/
def canonicalWitnessStage (U : LCarrier.{u}) : LCarrier.{u} :=
  stageLCarrier (canonicalWitnessStageOrdinal U)

/-- The internally represented canonical order on the witness stage. -/
def canonicalWitnessOrder (U : LCarrier.{u}) : LCarrier.{u} :=
  (stageHistoryData (canonicalWitnessStageOrdinal U)).relation

theorem seed_subset_canonicalWitnessStage (U : LCarrier.{u}) :
    U.1 ⊆ (canonicalWitnessStage U).1 := by
  intro x hx
  change x ∈ LStageZF (canonicalWitnessStageOrdinal U)
  exact (LStageZF_isTransitive (canonicalWitnessStageOrdinal U)).mem_trans
    hx (Constructible.mem_LStageZF_firstStage U.1 U.2)

/-- The chosen stage order is represented by an actual member of `L`. -/
theorem canonicalWitnessOrder_internallyWellOrders (U : LCarrier.{u}) :
    InternallyWellOrders (canonicalWitnessOrder U)
      (canonicalWitnessStage U) := by
  let ordinal := canonicalWitnessStageOrdinal U
  have hsystem := historyStageGraphs_coherent (Order.succ ordinal)
  simpa only [canonicalWitnessOrder, canonicalWitnessStage, ordinal,
    historyStageGraphs_last, lastStageIndex_val] using
      hsystem.wellOrders (lastStageIndex ordinal)

/-- The singleton-family graph attached to one rudimentary relation and one
parameter tuple.  Its input is the corresponding witness set; its unique
output, when a witness exists, is the canonical least witness. -/
def canonicalRudimentaryWitnessGraph
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) n) : LCarrier.{u} :=
  let candidates := rudimentaryWitnessSet U relation params
  canonicalLeastChoiceGraph (singletonLCarrier candidates)
    (canonicalWitnessStage U) (canonicalWitnessOrder U)

/-- The singleton candidate family is bounded by the canonical witness
stage. -/
theorem rudimentaryWitnessFamilySubsets
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) n) :
    FamilySubsets
      (singletonLCarrier (rudimentaryWitnessSet U relation params))
      (canonicalWitnessStage U) := by
  intro x hx z hz
  have hxEq : x = rudimentaryWitnessSet U relation params :=
    (mem_singletonLCarrier_iff
      (rudimentaryWitnessSet U relation params) x).mp hx
  subst x
  exact seed_subset_canonicalWitnessStage U
    (rudimentaryWitnessSet_subset U relation params hz)

/-- Exact minimum semantics of the singleton-family selector. -/
theorem graphRel_canonicalRudimentaryWitnessGraph_iff
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) n)
    (y : LCarrier.{u}) :
    GraphRel (canonicalRudimentaryWitnessGraph U relation params)
        (rudimentaryWitnessSet U relation params) y <->
      y.1 ∈ (rudimentaryWitnessSet U relation params).1 /\
        forall z : LCarrier.{u},
          z.1 ∈ (rudimentaryWitnessSet U relation params).1 ->
            Not (GraphRel (canonicalWitnessOrder U) z y) := by
  change
    GraphRel
        (canonicalLeastChoiceGraph
          (singletonLCarrier (rudimentaryWitnessSet U relation params))
          (canonicalWitnessStage U) (canonicalWitnessOrder U))
        (rudimentaryWitnessSet U relation params) y <-> _
  rw [graphRel_canonicalLeastChoiceGraph_iff
    (rudimentaryWitnessFamilySubsets U relation params)]
  simp only [mem_singletonLCarrier_iff, true_and]

/-- The graph selects exactly a relation witness in `U`, minimal among all
such witnesses in the canonical stage order. -/
theorem graphRel_canonicalRudimentaryWitnessGraph_relation_iff
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) n)
    (y : LCarrier.{u}) :
    GraphRel (canonicalRudimentaryWitnessGraph U relation params)
        (rudimentaryWitnessSet U relation params) y <->
      exists yU : ZFCarrier U.1,
        y.1 = yU.1 /\
          Godel.positiveTupleCode n
              (Delta0Formula.val (snoc params yU)) ∈ relation.1 /\
            forall zU : ZFCarrier U.1,
              Godel.positiveTupleCode n
                  (Delta0Formula.val (snoc params zU)) ∈ relation.1 ->
                Not (GraphRel (canonicalWitnessOrder U)
                  ⟨zU.1, mem_L_of_mem zU.2 U.2⟩ y) := by
  rw [graphRel_canonicalRudimentaryWitnessGraph_iff]
  constructor
  · rintro ⟨hyCandidate, hminimal⟩
    have hyU : y.1 ∈ U.1 :=
      rudimentaryWitnessSet_subset U relation params hyCandidate
    let yU : ZFCarrier U.1 := ⟨y.1, hyU⟩
    refine ⟨yU, rfl,
      (mem_rudimentaryWitnessSet_iff U relation params yU).mp
        hyCandidate, ?_⟩
    intro zU hzRelation
    let zL : LCarrier.{u} := ⟨zU.1, mem_L_of_mem zU.2 U.2⟩
    apply hminimal zL
    exact (mem_rudimentaryWitnessSet_iff U relation params zU).mpr
      hzRelation
  · rintro ⟨yU, hyEq, hyRelation, hminimal⟩
    have hyCandidateU :=
      (mem_rudimentaryWitnessSet_iff U relation params yU).mpr
        hyRelation
    have hyCandidate :
        y.1 ∈ (rudimentaryWitnessSet U relation params).1 := by
      simpa only [hyEq] using hyCandidateU
    refine ⟨hyCandidate, ?_⟩
    intro z hzCandidate
    have hzU : z.1 ∈ U.1 :=
      rudimentaryWitnessSet_subset U relation params hzCandidate
    let zU : ZFCarrier U.1 := ⟨z.1, hzU⟩
    have hzRelation :=
      (mem_rudimentaryWitnessSet_iff U relation params zU).mp
        hzCandidate
    have hzMinimal := hminimal zU hzRelation
    have hzEq : (⟨zU.1, mem_L_of_mem zU.2 U.2⟩ : LCarrier.{u}) = z :=
      Subtype.ext rfl
    simpa only [hzEq] using hzMinimal

/-- A nonempty represented relation has exactly one canonically selected
witness, and the selector is an actual Kuratowski graph in `L`. -/
theorem existsUnique_canonicalRudimentaryWitnessGraph
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) n)
    (hexists : exists x : ZFCarrier U.1,
      Godel.positiveTupleCode n
        (Delta0Formula.val (snoc params x)) ∈ relation.1) :
    ∃! y : LCarrier.{u},
      GraphRel (canonicalRudimentaryWitnessGraph U relation params)
        (rudimentaryWitnessSet U relation params) y := by
  let candidates := rudimentaryWitnessSet U relation params
  let family := singletonLCarrier candidates
  have hsub : FamilySubsets family (canonicalWitnessStage U) := by
    simpa only [family, candidates] using
      rudimentaryWitnessFamilySubsets U relation params
  have hnonempty : forall x : LCarrier.{u}, x.1 ∈ family.1 ->
      exists y : LCarrier.{u}, y.1 ∈ x.1 := by
    intro x hx
    have hxEq : x = candidates :=
      (mem_singletonLCarrier_iff candidates x).mp hx
    subst x
    rcases hexists with ⟨w, hw⟩
    let wL : LCarrier.{u} := ⟨w.1, mem_L_of_mem w.2 U.2⟩
    refine ⟨wL, ?_⟩
    exact (mem_rudimentaryWitnessSet_iff U relation params w).mpr hw
  have hcandidates : candidates.1 ∈ family.1 :=
    (mem_singletonLCarrier_iff candidates candidates).mpr rfl
  simpa only [canonicalRudimentaryWitnessGraph, candidates, family] using
    existsUnique_graphRel_canonicalLeastChoiceGraph
      (canonicalWitnessOrder_internallyWellOrders U) hsub hnonempty
      candidates hcandidates

end

end Constructible.Model
