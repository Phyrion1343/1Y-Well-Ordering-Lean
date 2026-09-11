/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Model
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Ordinals
public import Mathlib.Tactic.FinCases

/-!
# First-order formulations of CH and GCH

This file defines the Continuum Hypothesis and the Generalized Continuum
Hypothesis as parameter-free formulas in the membership language.  Cardinal
comparison is expressed internally through sets of Kuratowski pairs coding
bijections; no ambient Lean cardinal is used in either sentence.

The formula fragments are accompanied by semantics for an arbitrary type and
an arbitrary binary membership relation.  Consequently the final semantic
theorems can later be instantiated both in `LCarrier` and in other
set-theoretic structures.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

/-! ## Semantic relations -/

def IsEmptySet {A : Type u} (E : A → A → Prop) (x : A) : Prop :=
  ∀ z : A, ¬E z x

def IsSubsetOf {A : Type u} (E : A → A → Prop) (x y : A) : Prop :=
  ∀ z : A, E z x → E z y

def IsSingletonOf {A : Type u} (E : A → A → Prop)
    (singleton x : A) : Prop :=
  E x singleton ∧ ∀ z : A, E z singleton → z = x

def IsUnorderedPairOf {A : Type u} (E : A → A → Prop)
    (pair x y : A) : Prop :=
  E x pair ∧ E y pair ∧
    ∀ z : A, E z pair → z = x ∨ z = y

def IsKuratowskiPairOf {A : Type u} (E : A → A → Prop)
    (pair x y : A) : Prop :=
  (∃ singleton : A,
      E singleton pair ∧ IsSingletonOf E singleton x) ∧
    (∃ unordered : A,
      E unordered pair ∧ IsUnorderedPairOf E unordered x y) ∧
    ∀ z : A, E z pair →
      IsSingletonOf E z x ∨ IsUnorderedPairOf E z x y

def GraphValue {A : Type u} (E : A → A → Prop)
    (graph x y : A) : Prop :=
  ∃ pair : A, E pair graph ∧ IsKuratowskiPairOf E pair x y

def HasUniqueImage {A : Type u} (E : A → A → Prop)
    (graph x codomain : A) : Prop :=
  ∃ y : A, E y codomain ∧ GraphValue E graph x y ∧
    ∀ z : A, E z codomain → GraphValue E graph x z → z = y

def HasUniquePreimage {A : Type u} (E : A → A → Prop)
    (graph domain y : A) : Prop :=
  ∃ x : A, E x domain ∧ GraphValue E graph x y ∧
    ∀ z : A, E z domain → GraphValue E graph z y → z = x

def IsGraphBetween {A : Type u} (E : A → A → Prop)
    (graph domain codomain : A) : Prop :=
  ∀ pair : A, E pair graph →
    ∃ x : A, E x domain ∧
      ∃ y : A, E y codomain ∧ IsKuratowskiPairOf E pair x y

def IsBijection {A : Type u} (E : A → A → Prop)
    (graph domain codomain : A) : Prop :=
  IsGraphBetween E graph domain codomain ∧
    (∀ x : A, E x domain → HasUniqueImage E graph x codomain) ∧
      ∀ y : A, E y codomain → HasUniquePreimage E graph domain y

def Equinumerous {A : Type u} (E : A → A → Prop) (x y : A) : Prop :=
  ∃ graph : A, IsBijection E graph x y

/-! ## Formula fragments for pairs and bijections -/

/-- `s set` behaves as the singleton of `s x`. -/
def singletonAt {n : Nat} (set x : Fin n) : FOFormula n :=
  .conj (.mem x set)
    (FOFormula.boundedAll set
      (.eq (Fin.last n) x.castSucc))

@[simp]
theorem satisfies_singletonAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (set x : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (singletonAt set x) s ↔
      IsSingletonOf E (s set) (s x) := by
  simp only [singletonAt, FOFormula.Satisfies,
    FOFormula.satisfies_boundedAll, snoc_last, snoc_castSucc,
    IsSingletonOf]

/-- `s pair` behaves as the unordered pair of `s x` and `s y`. -/
def unorderedPairAt {n : Nat} (pair x y : Fin n) : FOFormula n :=
  .conj (.mem x pair)
    (.conj (.mem y pair)
      (FOFormula.boundedAll pair
        (FOFormula.disj
          (.eq (Fin.last n) x.castSucc)
          (.eq (Fin.last n) y.castSucc))))

@[simp]
theorem satisfies_unorderedPairAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (pair x y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (unorderedPairAt pair x y) s ↔
      IsUnorderedPairOf E (s pair) (s x) (s y) := by
  simp only [unorderedPairAt, FOFormula.Satisfies,
    FOFormula.satisfies_boundedAll, FOFormula.satisfies_disj,
    snoc_last, snoc_castSucc, IsUnorderedPairOf]

/-- `s pair` behaves as the Kuratowski ordered pair of `s x` and `s y`. -/
def kuratowskiPairAt {n : Nat} (pair x y : Fin n) : FOFormula n :=
  .conj
    (FOFormula.boundedEx pair
      (singletonAt (Fin.last n) x.castSucc))
    (.conj
      (FOFormula.boundedEx pair
        (unorderedPairAt (Fin.last n) x.castSucc y.castSucc))
      (FOFormula.boundedAll pair
        (FOFormula.disj
          (singletonAt (Fin.last n) x.castSucc)
          (unorderedPairAt (Fin.last n) x.castSucc y.castSucc))))

@[simp]
theorem satisfies_kuratowskiPairAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (pair x y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (kuratowskiPairAt pair x y) s ↔
      IsKuratowskiPairOf E (s pair) (s x) (s y) := by
  simp only [kuratowskiPairAt, FOFormula.Satisfies,
    FOFormula.satisfies_boundedEx, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_disj, satisfies_singletonAt,
    satisfies_unorderedPairAt, snoc_last, snoc_castSucc,
    IsKuratowskiPairOf]

/-- The graph `s graph` contains the ordered pair `(s x, s y)`. -/
def graphValueAt {n : Nat} (graph x y : Fin n) : FOFormula n :=
  .ex (.conj
    (.mem (Fin.last n) graph.castSucc)
    (kuratowskiPairAt
      (Fin.last n) x.castSucc y.castSucc))

@[simp]
theorem satisfies_graphValueAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (graph x y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (graphValueAt graph x y) s ↔
      GraphValue E (s graph) (s x) (s y) := by
  simp only [graphValueAt, FOFormula.Satisfies,
    satisfies_kuratowskiPairAt, snoc_last, snoc_castSucc,
    GraphValue]

/-- The graph has exactly one value in `codomain` at `x`. -/
def uniqueImageAt {n : Nat}
    (graph x codomain : Fin n) : FOFormula n :=
  FOFormula.boundedEx codomain
    (.conj
      (graphValueAt graph.castSucc x.castSucc (Fin.last n))
      (FOFormula.boundedAll codomain.castSucc
        (FOFormula.imp
          (graphValueAt graph.castSucc.castSucc
            x.castSucc.castSucc (Fin.last (n + 1)))
          (.eq (Fin.last (n + 1)) (Fin.last n).castSucc))))

@[simp]
theorem satisfies_uniqueImageAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (graph x codomain : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (uniqueImageAt graph x codomain) s ↔
      HasUniqueImage E (s graph) (s x) (s codomain) := by
  simp only [uniqueImageAt, FOFormula.satisfies_boundedEx,
    FOFormula.Satisfies, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_imp, satisfies_graphValueAt,
    snoc_last, snoc_castSucc, HasUniqueImage]

/-- The graph has exactly one preimage in `domain` at `y`. -/
def uniquePreimageAt {n : Nat}
    (graph domain y : Fin n) : FOFormula n :=
  FOFormula.boundedEx domain
    (.conj
      (graphValueAt graph.castSucc (Fin.last n) y.castSucc)
      (FOFormula.boundedAll domain.castSucc
        (FOFormula.imp
          (graphValueAt graph.castSucc.castSucc
            (Fin.last (n + 1)) y.castSucc.castSucc)
          (.eq (Fin.last (n + 1)) (Fin.last n).castSucc))))

@[simp]
theorem satisfies_uniquePreimageAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (graph domain y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (uniquePreimageAt graph domain y) s ↔
      HasUniquePreimage E (s graph) (s domain) (s y) := by
  simp only [uniquePreimageAt, FOFormula.satisfies_boundedEx,
    FOFormula.Satisfies, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_imp, satisfies_graphValueAt,
    snoc_last, snoc_castSucc, HasUniquePreimage]

/-- Every member of `graph` is a pair from `domain × codomain`. -/
def graphBetweenAt {n : Nat}
    (graph domain codomain : Fin n) : FOFormula n :=
  FOFormula.boundedAll graph
    (FOFormula.boundedEx domain.castSucc
      (FOFormula.boundedEx codomain.castSucc.castSucc
        (kuratowskiPairAt
          (Fin.last n).castSucc.castSucc
          (Fin.last (n + 1)).castSucc
          (Fin.last (n + 2)))))

@[simp]
theorem satisfies_graphBetweenAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (graph domain codomain : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (graphBetweenAt graph domain codomain) s ↔
      IsGraphBetween E (s graph) (s domain) (s codomain) := by
  simp only [graphBetweenAt, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_boundedEx, satisfies_kuratowskiPairAt,
    snoc_last, snoc_castSucc, IsGraphBetween]

/-- `graph` codes a bijection from `domain` onto `codomain`. -/
def bijectionAt {n : Nat}
    (graph domain codomain : Fin n) : FOFormula n :=
  .conj (graphBetweenAt graph domain codomain)
    (.conj
      (FOFormula.boundedAll domain
        (uniqueImageAt graph.castSucc
          (Fin.last n) codomain.castSucc))
      (FOFormula.boundedAll codomain
        (uniquePreimageAt graph.castSucc
          domain.castSucc (Fin.last n))))

@[simp]
theorem satisfies_bijectionAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (graph domain codomain : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (bijectionAt graph domain codomain) s ↔
      IsBijection E (s graph) (s domain) (s codomain) := by
  simp only [bijectionAt, FOFormula.Satisfies,
    satisfies_graphBetweenAt, FOFormula.satisfies_boundedAll,
    satisfies_uniqueImageAt, satisfies_uniquePreimageAt,
    snoc_last, snoc_castSucc, IsBijection]

/-- There is a set coding a bijection between `x` and `y`. -/
def equinumerousAt {n : Nat} (x y : Fin n) : FOFormula n :=
  .ex (bijectionAt (Fin.last n) x.castSucc y.castSucc)

@[simp]
theorem satisfies_equinumerousAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (x y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (equinumerousAt x y) s ↔
      Equinumerous E (s x) (s y) := by
  simp only [equinumerousAt, FOFormula.Satisfies,
    satisfies_bijectionAt, snoc_last, snoc_castSucc,
    Equinumerous]

/-! ## Subsets, ordinals, and cardinals -/

def IsTransitiveSet {A : Type u} (E : A → A → Prop) (x : A) : Prop :=
  ∀ y : A, E y x → ∀ z : A, E z y → E z x

def IsVonNeumannOrdinal {A : Type u} (E : A → A → Prop) (x : A) : Prop :=
  IsTransitiveSet E x ∧
    ∀ y : A, E y x → IsTransitiveSet E y

def IsPowerSetOf {A : Type u} (E : A → A → Prop)
    (base power : A) : Prop :=
  ∀ x : A, E x power ↔ IsSubsetOf E x base

def IsSuccessorSetOf {A : Type u} (E : A → A → Prop)
    (successor x : A) : Prop :=
  ∀ z : A, E z successor ↔ E z x ∨ z = x

def IsInductiveSet {A : Type u} (E : A → A → Prop) (w : A) : Prop :=
  (∃ empty : A, IsEmptySet E empty ∧ E empty w) ∧
    ∀ x : A, E x w →
      ∃ successor : A,
        IsSuccessorSetOf E successor x ∧ E successor w

def IsOmega {A : Type u} (E : A → A → Prop) (omega : A) : Prop :=
  IsInductiveSet E omega ∧
    ∀ w : A, IsInductiveSet E w → IsSubsetOf E omega w

def IsCardinal {A : Type u} (E : A → A → Prop) (kappa : A) : Prop :=
  IsVonNeumannOrdinal E kappa ∧
    ∀ alpha : A, E alpha kappa →
      ¬Equinumerous E alpha kappa

def IsSuccessorCardinal {A : Type u} (E : A → A → Prop)
    (kappa next : A) : Prop :=
  IsCardinal E kappa ∧ IsCardinal E next ∧ E kappa next ∧
    ¬∃ intermediate : A,
      IsCardinal E intermediate ∧
        E kappa intermediate ∧ E intermediate next

/-- Every member of `x` is a member of `y`. -/
def subsetAt {n : Nat} (x y : Fin n) : FOFormula n :=
  FOFormula.all
    (FOFormula.imp
      (.mem (Fin.last n) x.castSucc)
      (.mem (Fin.last n) y.castSucc))

@[simp]
theorem satisfies_subsetAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (x y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (subsetAt x y) s ↔
      IsSubsetOf E (s x) (s y) := by
  simp only [subsetAt, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, FOFormula.Satisfies,
    snoc_last, snoc_castSucc, IsSubsetOf]

/-- `power` contains exactly the subsets of `base`. -/
def powerSetAt {n : Nat} (power base : Fin n) : FOFormula n :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last n) power.castSucc)
      (subsetAt (Fin.last n) base.castSucc))

@[simp]
theorem satisfies_powerSetAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (power base : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (powerSetAt power base) s ↔
      IsPowerSetOf E (s base) (s power) := by
  simp only [powerSetAt, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_subsetAt, snoc_last, snoc_castSucc,
    IsPowerSetOf]

private theorem satisfies_isOrdinal_singleton
    {A : Type u} (E : A → A → Prop) (x : A) :
    FOFormula.Satisfies E OrdinalFormula.isOrdinal ![x] ↔
      IsVonNeumannOrdinal E x := by
  simp only [OrdinalFormula.isOrdinal, FOFormula.Satisfies,
    OrdinalFormula.transitive, OrdinalFormula.membersTransitive,
    FOFormula.satisfies_boundedAll, Matrix.cons_val_zero,
    snoc_last, IsVonNeumannOrdinal,
    IsTransitiveSet]
  rw [show (0 : Fin 3) = (0 : Fin 1).castSucc.castSucc by decide]
  rw [show (1 : Fin 4) = (Fin.last 1).castSucc.castSucc by decide]
  simp only [snoc_castSucc, snoc_last, Matrix.cons_val_zero]

/-- Put the von Neumann ordinal predicate at coordinate `i`. -/
def isOrdinalAt {n : Nat} (i : Fin n) : FOFormula n :=
  FOFormula.rename (fun _ : Fin 1 => i) OrdinalFormula.isOrdinal

@[simp]
theorem satisfies_isOrdinalAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (i : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (isOrdinalAt i) s ↔
      IsVonNeumannOrdinal E (s i) := by
  rw [isOrdinalAt, FOFormula.satisfies_rename]
  have hassignment : (fun _ : Fin 1 => s i) = ![s i] := by
    funext j
    exact Fin.eq_zero j ▸ rfl
  rw [hassignment, satisfies_isOrdinal_singleton]

/-- Coordinate `i` has no members. -/
def emptySetAt {n : Nat} (i : Fin n) : FOFormula n :=
  FOFormula.all (.neg (.mem (Fin.last n) i.castSucc))

@[simp]
theorem satisfies_emptySetAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (i : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (emptySetAt i) s ↔
      IsEmptySet E (s i) := by
  simp only [emptySetAt, FOFormula.satisfies_all,
    FOFormula.Satisfies, snoc_last, snoc_castSucc,
    IsEmptySet]

/-- `successor` is the von Neumann successor of `x`. -/
def successorSetAt {n : Nat} (successor x : Fin n) : FOFormula n :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last n) successor.castSucc)
      (FOFormula.disj
        (.mem (Fin.last n) x.castSucc)
        (.eq (Fin.last n) x.castSucc)))

@[simp]
theorem satisfies_successorSetAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (successor x : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (successorSetAt successor x) s ↔
      IsSuccessorSetOf E (s successor) (s x) := by
  simp only [successorSetAt, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.satisfies_disj,
    FOFormula.Satisfies, snoc_last, snoc_castSucc,
    IsSuccessorSetOf]

/-- Coordinate `i` is inductive. -/
def inductiveSetAt {n : Nat} (i : Fin n) : FOFormula n :=
  .conj
    (.ex (.conj
      (emptySetAt (Fin.last n))
      (.mem (Fin.last n) i.castSucc)))
    (FOFormula.all
      (FOFormula.imp
        (.mem (Fin.last n) i.castSucc)
        (.ex (.conj
          (successorSetAt
            (Fin.last (n + 1)) (Fin.last n).castSucc)
          (.mem (Fin.last (n + 1)) i.castSucc.castSucc)))))

@[simp]
theorem satisfies_inductiveSetAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (i : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (inductiveSetAt i) s ↔
      IsInductiveSet E (s i) := by
  simp only [inductiveSetAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_emptySetAt, satisfies_successorSetAt,
    snoc_last, snoc_castSucc, IsInductiveSet]

/-- Coordinate `i` is the least inductive set. -/
def omegaAt {n : Nat} (i : Fin n) : FOFormula n :=
  .conj
    (inductiveSetAt i)
    (FOFormula.all
      (FOFormula.imp
        (inductiveSetAt (Fin.last n))
        (subsetAt i.castSucc (Fin.last n))))

@[simp]
theorem satisfies_omegaAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (i : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (omegaAt i) s ↔
      IsOmega E (s i) := by
  simp only [omegaAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_inductiveSetAt, satisfies_subsetAt,
    snoc_last, snoc_castSucc, IsOmega]

/-- `kappa` is an initial ordinal, hence an internal cardinal. -/
def cardinalAt {n : Nat} (kappa : Fin n) : FOFormula n :=
  .conj
    (isOrdinalAt kappa)
    (FOFormula.boundedAll kappa
      (.neg (equinumerousAt (Fin.last n) kappa.castSucc)))

@[simp]
theorem satisfies_cardinalAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (kappa : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (cardinalAt kappa) s ↔
      IsCardinal E (s kappa) := by
  simp only [cardinalAt, FOFormula.Satisfies,
    satisfies_isOrdinalAt, FOFormula.satisfies_boundedAll,
    satisfies_equinumerousAt, snoc_last, snoc_castSucc,
    IsCardinal]

/-- `next` is the least internal cardinal strictly above `kappa`. -/
def successorCardinalAt {n : Nat}
    (kappa next : Fin n) : FOFormula n :=
  .conj (cardinalAt kappa)
    (.conj (cardinalAt next)
      (.conj (.mem kappa next)
        (.neg (.ex
          (.conj (cardinalAt (Fin.last n))
            (.conj
              (.mem kappa.castSucc (Fin.last n))
              (.mem (Fin.last n) next.castSucc)))))))

@[simp]
theorem satisfies_successorCardinalAt
    {A : Type u} (E : A → A → Prop) {n : Nat}
    (kappa next : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (successorCardinalAt kappa next) s ↔
      IsSuccessorCardinal E (s kappa) (s next) := by
  simp only [successorCardinalAt, FOFormula.Satisfies,
    satisfies_cardinalAt, snoc_last, snoc_castSucc,
    IsSuccessorCardinal]

/-! ## CH and GCH -/

/-- Semantic form of the Continuum Hypothesis in a membership structure. -/
def ModelsCH {A : Type u} (E : A → A → Prop) : Prop :=
  ∃ omega next power : A,
    IsOmega E omega ∧
      IsSuccessorCardinal E omega next ∧
      IsPowerSetOf E omega power ∧
      Equinumerous E power next

/-- Semantic form of the Generalized Continuum Hypothesis. -/
def ModelsGCH {A : Type u} (E : A → A → Prop) : Prop :=
  ∃ omega : A,
    IsOmega E omega ∧ IsCardinal E omega ∧
      ∀ kappa : A,
        (IsCardinal E kappa ∧ IsSubsetOf E omega kappa) →
          ∃ next power : A,
            IsSuccessorCardinal E kappa next ∧
              IsPowerSetOf E kappa power ∧
              Equinumerous E power next

/-- Layout `(omega, omegaOne, powerOmega)`. -/
def chCoreFormula : FOFormula 3 :=
  .conj (omegaAt (0 : Fin 3))
    (.conj (successorCardinalAt (0 : Fin 3) (1 : Fin 3))
      (.conj (powerSetAt (2 : Fin 3) (0 : Fin 3))
        (equinumerousAt (2 : Fin 3) (1 : Fin 3))))

/-- The parameter-free first-order formula `P(omega) ≈ omegaOne`. -/
def chFormula : FOFormula 0 :=
  .ex (.ex (.ex chCoreFormula))

private theorem ch_assignment
    {A : Type u} (omega next power : A) :
    snoc (snoc (snoc (fun i : Fin 0 => Fin.elim0 i) omega)
      next) power = ![omega, next, power] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_chFormula {A : Type u} (E : A → A → Prop) :
    FOFormula.Satisfies E chFormula
        (fun i : Fin 0 => Fin.elim0 i) ↔
      ModelsCH E := by
  simp only [chFormula, FOFormula.Satisfies]
  apply exists_congr
  intro omega
  apply exists_congr
  intro next
  apply exists_congr
  intro power
  rw [ch_assignment]
  simp only [chCoreFormula, FOFormula.Satisfies,
    satisfies_omegaAt, satisfies_successorCardinalAt,
    satisfies_powerSetAt, satisfies_equinumerousAt,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- With `omega` at coordinate zero, assert GCH at every internal cardinal
containing it. -/
def gchAtOmegaFormula : FOFormula 1 :=
  .conj (omegaAt (0 : Fin 1))
    (.conj (cardinalAt (0 : Fin 1))
      (FOFormula.all
        (FOFormula.imp
          (.conj
            (cardinalAt (Fin.last 1))
            (subsetAt (0 : Fin 1).castSucc (Fin.last 1)))
          (.ex (.ex
            (.conj
              (successorCardinalAt (1 : Fin 4) (2 : Fin 4))
              (.conj
                (powerSetAt (3 : Fin 4) (1 : Fin 4))
                (equinumerousAt (3 : Fin 4) (2 : Fin 4)))))))))

/-- The parameter-free first-order formulation of GCH. -/
def gchFormula : FOFormula 0 :=
  .ex gchAtOmegaFormula

private theorem gch_omega_assignment {A : Type u} (omega : A) :
    snoc (fun i : Fin 0 => Fin.elim0 i) omega = ![omega] := by
  funext i
  fin_cases i
  rfl

private theorem gch_kappa_assignment {A : Type u}
    (omega kappa : A) :
    snoc ![omega] kappa = ![omega, kappa] := by
  funext i
  fin_cases i <;> rfl

private theorem gch_witness_assignment {A : Type u}
    (omega kappa next power : A) :
    snoc (snoc ![omega, kappa] next) power =
      ![omega, kappa, next, power] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_gchFormula {A : Type u} (E : A → A → Prop) :
    FOFormula.Satisfies E gchFormula
        (fun i : Fin 0 => Fin.elim0 i) ↔
      ModelsGCH E := by
  simp only [gchFormula, FOFormula.Satisfies]
  apply exists_congr
  intro omega
  rw [gch_omega_assignment]
  simp only [gchAtOmegaFormula, FOFormula.Satisfies,
    satisfies_omegaAt, satisfies_cardinalAt,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    Matrix.cons_val_zero]
  constructor
  · rintro ⟨homega, homegaCardinal, hgeneral⟩
    refine ⟨homega, homegaCardinal, ?_⟩
    intro kappa hkappa
    have hbody := hgeneral kappa
    rw [gch_kappa_assignment] at hbody
    simp only [satisfies_subsetAt] at hbody
    rcases hbody hkappa with ⟨next, power, hnext⟩
    rw [gch_witness_assignment] at hnext
    refine ⟨next, power, ?_⟩
    simpa only [FOFormula.Satisfies,
      satisfies_successorCardinalAt, satisfies_powerSetAt,
      satisfies_equinumerousAt, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] using hnext
  · rintro ⟨homega, homegaCardinal, hgeneral⟩
    refine ⟨homega, homegaCardinal, ?_⟩
    intro kappa
    rw [gch_kappa_assignment]
    simp only [satisfies_subsetAt]
    intro hkappa
    rcases hgeneral kappa hkappa with ⟨next, power, hnext⟩
    refine ⟨next, power, ?_⟩
    rw [gch_witness_assignment]
    simpa only [FOFormula.Satisfies,
      satisfies_successorCardinalAt, satisfies_powerSetAt,
      satisfies_equinumerousAt, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] using hnext

/-- CH as a Mathlib sentence in the first-order language of membership. -/
def chSentence : FirstOrder.Language.setTheory.Sentence :=
  Model.toSentence chFormula

/-- GCH as a Mathlib sentence in the first-order language of membership. -/
def gchSentence : FirstOrder.Language.setTheory.Sentence :=
  Model.toSentence gchFormula

/-- The translated CH sentence has exactly the relation-parametric semantics
`ModelsCH`. -/
@[simp]
theorem realizes_chSentence_iff {A : Type u} (E : A → A → Prop) :
    Model.realizes E chSentence (fun i : Fin 0 => Fin.elim0 i) ↔
      ModelsCH E := by
  rw [chSentence, Model.realizes_toBoundedFormula,
    satisfies_chFormula]

/-- The translated GCH sentence has exactly the relation-parametric semantics
`ModelsGCH`. -/
@[simp]
theorem realizes_gchSentence_iff {A : Type u} (E : A → A → Prop) :
    Model.realizes E gchSentence (fun i : Fin 0 => Fin.elim0 i) ↔
      ModelsGCH E := by
  rw [gchSentence, Model.realizes_toBoundedFormula,
    satisfies_gchFormula]

end Constructible.ContinuumFormula
