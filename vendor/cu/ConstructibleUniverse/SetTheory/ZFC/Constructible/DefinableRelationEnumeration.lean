/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FormulaSyntaxCode
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Countable enumeration of definable relations

For a fixed arity `n`, this file implements the external enumeration argument
corresponding to the countability result for definable relations.  The input is
the explicit coding and decoding of formulas in `FormulaSyntaxCode.lean`, and
the key semantic fact is `mem_Df_iff_exists_formula`.

The resulting map `definableRelationEnumerate E n` is an extensionally
equivalent `E(a,n,m)`-style enumeration: a valid code is sent to the relation
defined by the decoded formula, while an invalid code is sent to the empty
relation.  Its numerical coding is not claimed to agree pointwise with the
textbook's prime-power coding.  What is proved is the exact mathematical
content used here: it is a total map from the metatheoretic natural numbers
onto the subtype of relations belonging to `Df E n`.

We then assign to every definable relation the least code at which it occurs.
This gives an injection into `Nat`, and hence the cardinal bound
`#(DefinableRelation E n) <= aleph0`.

This is deliberately an external Lean enumeration.  Nothing in this file
asserts that it is represented by a function which is itself an internal
`ZFSet`, or proves the separate absoluteness theorem for `E` and `Df` between
transitive models.
-/

@[expose] public section

open Set
open scoped Cardinal

universe u

namespace Constructible

open FOFormulaCode

/-- The type of `n`-ary relations on `A` which belong to `Df E n`. -/
def DefinableRelation {A : Type u} (E : A -> A -> Prop) (n : Nat) :=
  {r : Rel A n // r ∈ Df E n}

/--
An identically false formula in every fixed free-variable context.  It is used
only to prove that the empty relation belongs to `Df`; it is not used as the
value of an invalid syntax decoder.
-/
def emptyRelationFormula (n : Nat) : FOFormula n :=
  .conj (defaultFormula n) (.neg (defaultFormula n))

/-- The empty relation, regarded as an element of `Df E n`. -/
def emptyDefinableRelation {A : Type u} (E : A -> A -> Prop)
    (n : Nat) : DefinableRelation E n :=
  ⟨∅, by
    rw [show (∅ : Rel A n) =
        FOFormula.semanticRel E (emptyRelationFormula n) by
      ext tuple
      simp [emptyRelationFormula]]
    exact semanticRel_mem_Df E (emptyRelationFormula n)⟩

/--
The textbook-style fixed-arity external enumeration of definable relations.
A valid formula code is sent to the relation defined by that formula; an
invalid code is sent to the empty relation.
-/
def definableRelationEnumerate {A : Type u} (E : A -> A -> Prop)
    (n code : Nat) : DefinableRelation E n :=
  match formulaNatDecode n code with
  | some formula =>
      ⟨FOFormula.semanticRel E formula, semanticRel_mem_Df E formula⟩
  | none => emptyDefinableRelation E n

/-- Every value of the external enumeration is a relation in `Df E n`. -/
@[simp]
theorem definableRelationEnumerate_mem_Df {A : Type u}
    (E : A -> A -> Prop) (n code : Nat) :
    (definableRelationEnumerate E n code).1 ∈ Df E n :=
  (definableRelationEnumerate E n code).2

/-- At a genuine formula code, the relation enumeration gives its semantics. -/
@[simp]
theorem definableRelationEnumerate_formulaNatCode {A : Type u}
    (E : A -> A -> Prop) {n : Nat} (formula : FOFormula n) :
    (definableRelationEnumerate E n (formulaNatCode formula)).1 =
      FOFormula.semanticRel E formula := by
  simp [definableRelationEnumerate]

/-- An invalid formula code is sent exactly to the empty relation. -/
theorem definableRelationEnumerate_of_decode_eq_none {A : Type u}
    (E : A -> A -> Prop) (n code : Nat)
    (hcode : formulaNatDecode n code = none) :
    definableRelationEnumerate E n code = emptyDefinableRelation E n := by
  simp [definableRelationEnumerate, hcode]

/-- In particular, the underlying relation at an invalid code is empty. -/
theorem definableRelationEnumerate_val_of_decode_eq_none {A : Type u}
    (E : A -> A -> Prop) (n code : Nat)
    (hcode : formulaNatDecode n code = none) :
    (definableRelationEnumerate E n code).1 = (∅ : Rel A n) := by
  rw [definableRelationEnumerate_of_decode_eq_none E n code hcode]
  rfl

/-- Every relation in `Df E n` occurs in the fixed-arity enumeration. -/
theorem definableRelationEnumerate_surjective {A : Type u}
    (E : A -> A -> Prop) (n : Nat) :
    Function.Surjective (definableRelationEnumerate E n) := by
  rintro ⟨r, hr⟩
  rcases (mem_Df_iff_exists_formula (E := E)).mp hr with ⟨formula, rfl⟩
  refine ⟨formulaNatCode formula, ?_⟩
  apply Subtype.ext
  exact definableRelationEnumerate_formulaNatCode E formula

/-- The underlying values of the enumeration are exactly the relations in
`Df E n`.  This is the set-level form of the textbook enumeration theorem. -/
theorem range_definableRelationEnumerate_val {A : Type u}
    (E : A -> A -> Prop) (n : Nat) :
    Set.range (fun code => (definableRelationEnumerate E n code).1) =
      Df E n := by
  ext relation
  constructor
  · rintro ⟨code, rfl⟩
    exact definableRelationEnumerate_mem_Df E n code
  · intro hrelation
    let relationDf : DefinableRelation E n := ⟨relation, hrelation⟩
    rcases definableRelationEnumerate_surjective E n relationDf with
      ⟨code, hcode⟩
    exact ⟨code, congrArg Subtype.val hcode⟩

/-- Every definable relation has at least one code in the enumeration. -/
theorem exists_definableRelationCode {A : Type u} (E : A -> A -> Prop)
    (n : Nat) (relation : DefinableRelation E n) :
    ∃ code : Nat, definableRelationEnumerate E n code = relation :=
  definableRelationEnumerate_surjective E n relation

/-- The least natural-number code at which a definable relation occurs. -/
noncomputable def firstDefinableRelationCode {A : Type u}
    (E : A -> A -> Prop) (n : Nat) (relation : DefinableRelation E n) : Nat := by
  classical
  exact Nat.find (exists_definableRelationCode E n relation)

/-- The least code assigned to a relation really enumerates that relation. -/
@[simp]
theorem definableRelationEnumerate_firstCode {A : Type u}
    (E : A -> A -> Prop) (n : Nat) (relation : DefinableRelation E n) :
    definableRelationEnumerate E n (firstDefinableRelationCode E n relation) =
      relation := by
  classical
  exact Nat.find_spec (exists_definableRelationCode E n relation)

/-- The selected code is no larger than any other code for the same relation. -/
theorem firstDefinableRelationCode_minimal {A : Type u}
    (E : A -> A -> Prop) (n : Nat) (relation : DefinableRelation E n)
    {code : Nat} (hcode : definableRelationEnumerate E n code = relation) :
    firstDefinableRelationCode E n relation <= code := by
  classical
  exact Nat.find_min' (exists_definableRelationCode E n relation) hcode

/-- Least occurrence codes distinguish definable relations. -/
theorem firstDefinableRelationCode_injective {A : Type u}
    (E : A -> A -> Prop) (n : Nat) :
    Function.Injective (firstDefinableRelationCode E n) := by
  intro left right hcode
  have h := congrArg (definableRelationEnumerate E n) hcode
  simpa only [definableRelationEnumerate_firstCode] using h

/-- For every fixed arity, the type of relations in `Df E n` is countable. -/
theorem cardinal_mk_definableRelation_le_aleph0 {A : Type u}
    (E : A -> A -> Prop) (n : Nat) :
    #(DefinableRelation E n) <= Cardinal.aleph0 := by
  exact Cardinal.mk_le_aleph0_iff.mpr
    (firstDefinableRelationCode_injective E n).countable

end Constructible
