/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Model

/-!
# Restriction semantics for absoluteness

This file isolates the semantic core of the textbook definition of
absoluteness.  If `M` is an external class of sets, an `n`-ary relation is
absolute to `M` when the relation interpreted by its defining formula in
`M` is exactly the ambient relation restricted to tuples from `M`.

The corresponding definition for a function has two parts: its values on
arguments from `M` must lie in `M`, and its graph formula must have the
expected truth value in `M`.  The closure condition is stated explicitly;
correctness of a graph formula for candidate outputs already in `M` does not
by itself imply that the actual function value belongs to `M`.

No transitivity or set-theoretic axioms are needed for these semantic
equivalences.  Those hypotheses enter later, when closure and preservation
of recursive definitions are proved.
-/

@[expose] public section

open Set

universe u

namespace Constructible

namespace Model

/-! ## Relations and classes -/

/-- Every coordinate of `s` belongs to the external carrier `M`. -/
def TupleIn (M : Set ZFSet.{u}) {n : Nat}
    (s : Tuple ZFSet.{u} n) : Prop :=
  forall i, s i ∈ M

@[simp]
theorem tupleIn_snoc_iff {M : Set ZFSet.{u}} {n : Nat}
    {s : Tuple ZFSet.{u} n} {x : ZFSet.{u}} :
    TupleIn M (snoc s x) ↔ TupleIn M s ∧ x ∈ M := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      simpa using h i.castSucc
    · simpa using h (Fin.last n)
  · rintro ⟨hs, hx⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hx
    · simpa using hs j

/--
The formula `phi`, interpreted with all quantifiers restricted to `M`,
defines the ambient relation `R` on tuples whose coordinates lie in `M`.
-/
def RelationAbsoluteTo (M : Set ZFSet.{u}) {n : Nat}
    (R : Set (Tuple ZFSet.{u} n)) (phi : FOFormula n) : Prop :=
  forall s, TupleIn M s ->
    (SatisfiesIn M phi s ↔ s ∈ R)

/-- The relation obtained by interpreting `phi` in `M`. -/
def InterpretedRelation (M : Set ZFSet.{u}) {n : Nat}
    (phi : FOFormula n) : Set (Tuple ZFSet.{u} n) :=
  {s | TupleIn M s ∧ SatisfiesIn M phi s}

/-- The ambient relation `R`, restricted to tuples from `M`. -/
def RestrictedRelation (M : Set ZFSet.{u}) {n : Nat}
    (R : Set (Tuple ZFSet.{u} n)) : Set (Tuple ZFSet.{u} n) :=
  {s | TupleIn M s ∧ s ∈ R}

/--
Textbook restriction criterion for relations: interpretation in `M` is
exactly restriction of the ambient relation to `M`.
-/
theorem relationAbsoluteTo_iff_interpreted_eq_restricted
    {M : Set ZFSet.{u}} {n : Nat} {R : Set (Tuple ZFSet.{u} n)}
    {phi : FOFormula n} :
    RelationAbsoluteTo M R phi ↔
      InterpretedRelation M phi = RestrictedRelation M R := by
  constructor
  · intro h
    ext s
    constructor
    · rintro ⟨hs, hphi⟩
      exact ⟨hs, (h s hs).mp hphi⟩
    · rintro ⟨hs, hR⟩
      exact ⟨hs, (h s hs).mpr hR⟩
  · intro h s hs
    constructor
    · intro hphi
      have hsInterpreted : s ∈ InterpretedRelation M phi := ⟨hs, hphi⟩
      rw [h] at hsInterpreted
      exact hsInterpreted.2
    · intro hR
      have hsRestricted : s ∈ RestrictedRelation M R := ⟨hs, hR⟩
      rw [← h] at hsRestricted
      exact hsRestricted.2

/--
Per-formula absoluteness between two external carriers.  Parameters are
required to lie in the smaller carrier.
-/
def FormulaAbsoluteBetween (small big : Set ZFSet.{u}) {n : Nat}
    (phi : FOFormula n) : Prop :=
  forall s, TupleIn small s ->
    (SatisfiesIn small phi s ↔ SatisfiesIn big phi s)

/-- A unary class is absolute to `M` through the defining formula `phi`. -/
def ClassAbsoluteTo (M A : Set ZFSet.{u})
    (phi : FOFormula 1) : Prop :=
  forall x, x ∈ M ->
    (SatisfiesIn M phi ![x] ↔ x ∈ A)

/-- The class obtained by interpreting a unary formula in `M`. -/
def InterpretedClass (M : Set ZFSet.{u})
    (phi : FOFormula 1) : Set ZFSet.{u} :=
  {x | x ∈ M ∧ SatisfiesIn M phi ![x]}

/--
Textbook restriction criterion for classes: the interpretation of `A` in
`M` is `A ∩ M`.
-/
theorem classAbsoluteTo_iff_interpreted_eq_inter
    {M A : Set ZFSet.{u}} {phi : FOFormula 1} :
    ClassAbsoluteTo M A phi ↔ InterpretedClass M phi = A ∩ M := by
  constructor
  · intro h
    ext x
    constructor
    · rintro ⟨hxM, hphi⟩
      exact ⟨(h x hxM).mp hphi, hxM⟩
    · rintro ⟨hxA, hxM⟩
      exact ⟨hxM, (h x hxM).mpr hxA⟩
  · intro h x hxM
    constructor
    · intro hphi
      have hxInterpreted : x ∈ InterpretedClass M phi := ⟨hxM, hphi⟩
      rw [h] at hxInterpreted
      exact hxInterpreted.1
    · intro hxA
      have hxInter : x ∈ A ∩ M := ⟨hxA, hxM⟩
      rw [← h] at hxInter
      exact hxInter.2

/-! ## Functions -/

/--
The function `F`, with ambient domain `domain`, is absolute to `M` through
the formula `graph` when it is closed on arguments from `M` and `graph`
defines exactly its graph inside `M`.

The output is the final coordinate of the assignment to `graph`.
-/
def FunctionAbsoluteTo (M : Set ZFSet.{u}) {n : Nat}
    (domain : Set (Tuple ZFSet.{u} n))
    (F : Tuple ZFSet.{u} n -> ZFSet.{u})
    (graph : FOFormula (n + 1)) : Prop :=
  (forall s, TupleIn M s -> s ∈ domain -> F s ∈ M) ∧
    forall s y, TupleIn M s -> y ∈ M ->
      (SatisfiesIn M graph (snoc s y) ↔
        s ∈ domain ∧ y = F s)

/-- The graph obtained by interpreting `graph` in `M`. -/
def InterpretedFunctionGraph (M : Set ZFSet.{u}) {n : Nat}
    (graph : FOFormula (n + 1)) :
    Set (Tuple ZFSet.{u} n × ZFSet.{u}) :=
  {p | TupleIn M p.1 ∧ p.2 ∈ M ∧
    SatisfiesIn M graph (snoc p.1 p.2)}

/-- The ambient graph of `F`, restricted to arguments from `M`. -/
def RestrictedFunctionGraph (M : Set ZFSet.{u}) {n : Nat}
    (domain : Set (Tuple ZFSet.{u} n))
    (F : Tuple ZFSet.{u} n -> ZFSet.{u}) :
    Set (Tuple ZFSet.{u} n × ZFSet.{u}) :=
  {p | TupleIn M p.1 ∧ p.1 ∈ domain ∧ p.2 = F p.1}

/--
Textbook restriction criterion for functions.  In the reverse direction,
equality of the two graphs supplies the required output closure by applying
it to `(s, F s)`.
-/
theorem functionAbsoluteTo_iff_interpretedGraph_eq_restriction
    {M : Set ZFSet.{u}} {n : Nat}
    {domain : Set (Tuple ZFSet.{u} n)}
    {F : Tuple ZFSet.{u} n -> ZFSet.{u}}
    {graph : FOFormula (n + 1)} :
    FunctionAbsoluteTo M domain F graph ↔
      InterpretedFunctionGraph M graph =
        RestrictedFunctionGraph M domain F := by
  constructor
  · rintro ⟨hclosed, hgraph⟩
    ext p
    constructor
    · rintro ⟨hpM, hyM, hphi⟩
      exact ⟨hpM, (hgraph p.1 p.2 hpM hyM).mp hphi⟩
    · rintro ⟨hpM, hpDomain, hpValue⟩
      have hyM : p.2 ∈ M := by
        rw [hpValue]
        exact hclosed p.1 hpM hpDomain
      exact ⟨hpM, hyM,
        (hgraph p.1 p.2 hpM hyM).mpr ⟨hpDomain, hpValue⟩⟩
  · intro h
    constructor
    · intro s hs hDomain
      have hpRestricted :
          (s, F s) ∈ RestrictedFunctionGraph M domain F :=
        ⟨hs, hDomain, rfl⟩
      rw [← h] at hpRestricted
      exact hpRestricted.2.1
    · intro s y hs hy
      constructor
      · intro hphi
        have hpInterpreted :
            (s, y) ∈ InterpretedFunctionGraph M graph :=
          ⟨hs, hy, hphi⟩
        rw [h] at hpInterpreted
        exact hpInterpreted.2
      · rintro ⟨hDomain, hValue⟩
        have hpRestricted :
            (s, y) ∈ RestrictedFunctionGraph M domain F :=
          ⟨hs, hDomain, hValue⟩
        rw [← h] at hpRestricted
        exact hpRestricted.2.2

end Model

end Constructible
