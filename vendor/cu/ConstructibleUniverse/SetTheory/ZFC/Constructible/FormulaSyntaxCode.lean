/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteSequenceZF

/-!
# Goedel codes for the independent formula syntax

This file supplies a genuine enumeration of the intrinsically scoped syntax
`FOFormula n`.  It is separate from `FormulaGodel.lean`: that file represents
the relation defined by one fixed formula, whereas this file assigns a natural
number to the formula syntax itself.

The construction has three layers.

* `RawFormula` is an unscoped syntax tree whose variable names are natural
  numbers.  Its `Encodable` instance is a structural natural-number encoding.
* `formulaNatCode` erases the intrinsic scope information and encodes the raw
  tree.  `formulaNatDecode` restores a formula only when every variable is in
  scope.  The decoder is proved to be a left inverse.
* `PackedFormula = Sigma FOFormula` records the arity together with a formula,
  so formulas in different contexts also have distinct codes.

Finally, `formulaZFCode` and `packedFormulaZFCode` turn the natural codes into
von Neumann natural numbers in the internal `ZFSet` universe.  These codes are
members of the standard omega and are constructible.

This is the external syntax-enumeration layer needed before an object-language
uniform truth definition can be arithmetized.  It deliberately does not claim
that decoding or satisfaction is already represented by one `FOFormula`.
-/

@[expose] public section

universe u

namespace Constructible

namespace FOFormulaCode

/-! ## Unscoped syntax and scope checking -/

/--
An unscoped copy of the formula syntax.  Natural numbers replace `Fin n`
variables; quantifiers still use the convention that the new variable is the
last coordinate.
-/
inductive RawFormula : Type
  | mem (i j : Nat) : RawFormula
  | eq (i j : Nat) : RawFormula
  | neg (formula : RawFormula) : RawFormula
  | conj (left right : RawFormula) : RawFormula
  | ex (formula : RawFormula) : RawFormula
  deriving DecidableEq

/-- Forget the intrinsic scope proof carried by every variable. -/
def toRaw : {n : Nat} -> FOFormula n -> RawFormula
  | _, .mem i j => .mem i.1 j.1
  | _, .eq i j => .eq i.1 j.1
  | _, .neg formula => .neg (toRaw formula)
  | _, .conj left right => .conj (toRaw left) (toRaw right)
  | _, .ex formula => .ex (toRaw formula)

/-- Make a finite variable from a natural number exactly when it is in scope. -/
def finOfNat? (n i : Nat) : Option (Fin n) :=
  if hi : i < n then some ⟨i, hi⟩ else none

@[simp]
theorem finOfNat?_val {n : Nat} (i : Fin n) :
    finOfNat? n i.1 = some i := by
  simp [finOfNat?, i.2]

/--
Scope-check a raw tree in a context of size `n`.  The body of an existential
is checked in the extended context of size `n + 1`.
-/
def ofRaw : (n : Nat) -> RawFormula -> Option (FOFormula n)
  | n, .mem i j => do
      let i' <- finOfNat? n i
      let j' <- finOfNat? n j
      pure (.mem i' j')
  | n, .eq i j => do
      let i' <- finOfNat? n i
      let j' <- finOfNat? n j
      pure (.eq i' j')
  | n, .neg formula =>
      (ofRaw n formula).map FOFormula.neg
  | n, .conj left right => do
      let left' <- ofRaw n left
      let right' <- ofRaw n right
      pure (.conj left' right')
  | n, .ex formula =>
      (ofRaw (n + 1) formula).map FOFormula.ex

/-- Scope checking recovers every intrinsically scoped formula. -/
@[simp]
theorem ofRaw_toRaw {n : Nat} (formula : FOFormula n) :
    ofRaw n (toRaw formula) = some formula := by
  induction formula with
  | mem i j => simp [toRaw, ofRaw]
  | eq i j => simp [toRaw, ofRaw]
  | neg formula ih => simp [toRaw, ofRaw, ih]
  | conj left right ihLeft ihRight =>
      simp [toRaw, ofRaw, ihLeft, ihRight]
  | ex formula ih => simp [toRaw, ofRaw, ih]

/-- Erasing scope proofs loses no information at a fixed arity. -/
theorem toRaw_injective {n : Nat} :
    Function.Injective (toRaw : FOFormula n -> RawFormula) := by
  intro left right h
  have h' := congrArg (ofRaw n) h
  simpa using h'

/-! ## Natural-number codes -/

/-- Height of a raw syntax tree.  Atomic formulas have height zero. -/
def RawFormula.depth : RawFormula -> Nat
  | .mem _ _ => 0
  | .eq _ _ => 0
  | .neg formula => formula.depth + 1
  | .conj left right => max left.depth right.depth + 1
  | .ex formula => formula.depth + 1

/--
The structural natural-number code of a raw syntax tree.  The outer pair
records its height.  The inner pair records a constructor tag and its data;
recursive data are themselves complete codes.  Recording the height gives the
decoder an explicit structural recursion bound.
-/
def rawNatCode : RawFormula -> Nat
  | .mem i j => Nat.pair 0 (Nat.pair 0 (Nat.pair i j))
  | .eq i j => Nat.pair 0 (Nat.pair 1 (Nat.pair i j))
  | .neg formula =>
      Nat.pair (formula.depth + 1) (Nat.pair 2 (rawNatCode formula))
  | .conj left right =>
      Nat.pair (max left.depth right.depth + 1)
        (Nat.pair 3 (Nat.pair (rawNatCode left) (rawNatCode right)))
  | .ex formula =>
      Nat.pair (formula.depth + 1) (Nat.pair 4 (rawNatCode formula))

/-- Decode a raw syntax code using an explicit upper bound on tree height. -/
def rawNatDecodeAux : Nat -> Nat -> Option RawFormula
  | fuel, code =>
      let tagged := Nat.unpair (Nat.unpair code).2
      match tagged.1 with
      | 0 =>
          let indices := Nat.unpair tagged.2
          some (.mem indices.1 indices.2)
      | 1 =>
          let indices := Nat.unpair tagged.2
          some (.eq indices.1 indices.2)
      | 2 =>
          match fuel with
          | 0 => none
          | fuel + 1 => (rawNatDecodeAux fuel tagged.2).map RawFormula.neg
      | 3 =>
          match fuel with
          | 0 => none
          | fuel + 1 =>
              let children := Nat.unpair tagged.2
              (rawNatDecodeAux fuel children.1).bind fun left =>
                (rawNatDecodeAux fuel children.2).map fun right =>
                  .conj left right
      | 4 =>
          match fuel with
          | 0 => none
          | fuel + 1 => (rawNatDecodeAux fuel tagged.2).map RawFormula.ex
      | _ => none

/-- The height-bounded decoder recovers every code within its bound. -/
theorem rawNatDecodeAux_rawNatCode_of_depth_le (formula : RawFormula)
    {fuel : Nat} (h : formula.depth <= fuel) :
    rawNatDecodeAux fuel (rawNatCode formula) = some formula := by
  induction formula generalizing fuel with
  | mem i j =>
      rw [rawNatDecodeAux.eq_def]
      simp [rawNatCode]
  | eq i j =>
      rw [rawNatDecodeAux.eq_def]
      simp [rawNatCode]
  | neg formula ih =>
      cases fuel with
      | zero => simp [RawFormula.depth] at h
      | succ fuel =>
          have hFormula : formula.depth <= fuel := by
            exact Nat.succ_le_succ_iff.mp h
          simp [rawNatCode, rawNatDecodeAux, ih hFormula]
  | conj left right ihLeft ihRight =>
      cases fuel with
      | zero => simp [RawFormula.depth] at h
      | succ fuel =>
          have hMax : max left.depth right.depth <= fuel := by
            exact Nat.succ_le_succ_iff.mp h
          have hLeft : left.depth <= fuel :=
            (Nat.le_max_left _ _).trans hMax
          have hRight : right.depth <= fuel :=
            (Nat.le_max_right _ _).trans hMax
          simp [rawNatCode, rawNatDecodeAux,
            ihLeft hLeft, ihRight hRight]
  | ex formula ih =>
      cases fuel with
      | zero => simp [RawFormula.depth] at h
      | succ fuel =>
          have hFormula : formula.depth <= fuel := by
            exact Nat.succ_le_succ_iff.mp h
          simp [rawNatCode, rawNatDecodeAux, ih hFormula]

/-- A candidate decoder obtains its recursion bound from the encoded height. -/
def rawNatDecodeCandidate (code : Nat) : Option RawFormula :=
  rawNatDecodeAux (Nat.unpair code).1 code

@[simp]
theorem rawNatDecodeCandidate_rawNatCode (formula : RawFormula) :
    rawNatDecodeCandidate (rawNatCode formula) = some formula := by
  unfold rawNatDecodeCandidate
  have hDepth : (Nat.unpair (rawNatCode formula)).1 = formula.depth := by
    cases formula <;> simp [rawNatCode, RawFormula.depth]
  rw [hDepth]
  exact rawNatDecodeAux_rawNatCode_of_depth_le formula (Nat.le_refl _)

/-- Exact partial decoding: codes outside the encoder's range return `none`. -/
def rawNatDecode (code : Nat) : Option RawFormula :=
  (rawNatDecodeCandidate code).bind fun formula =>
    if rawNatCode formula = code then some formula else none

@[simp]
theorem rawNatDecode_rawNatCode (formula : RawFormula) :
    rawNatDecode (rawNatCode formula) = some formula := by
  simp [rawNatDecode]

/-- Raw syntax codes are injective. -/
theorem rawNatCode_injective : Function.Injective rawNatCode :=
  fun left right h => by
    have h' := congrArg rawNatDecode h
    simpa using h'

@[simp]
theorem rawNatCode_inj {left right : RawFormula} :
    rawNatCode left = rawNatCode right <-> left = right :=
  rawNatCode_injective.eq_iff

/-- The displayed structural code and exact decoder form an `Encodable`
instance; no generated or opaque coding function is involved. -/
instance rawFormulaEncodable : Encodable RawFormula where
  encode := rawNatCode
  decode := rawNatDecode
  encodek := rawNatDecode_rawNatCode

/-- Goedel code of a formula in one fixed variable context. -/
def formulaNatCode {n : Nat} (formula : FOFormula n) : Nat :=
  rawNatCode (toRaw formula)

/-- Decode and scope-check a formula code at arity `n`. -/
def formulaNatDecode (n code : Nat) : Option (FOFormula n) :=
  (rawNatDecode code).bind (ofRaw n)

/-- Formula decoding is a left inverse of formula coding. -/
@[simp]
theorem formulaNatDecode_formulaNatCode {n : Nat} (formula : FOFormula n) :
    formulaNatDecode n (formulaNatCode formula) = some formula := by
  simp [formulaNatDecode, formulaNatCode]

/-- Formula codes are injective at every fixed arity. -/
theorem formulaNatCode_injective {n : Nat} :
    Function.Injective (formulaNatCode : FOFormula n -> Nat) :=
  rawNatCode_injective.comp toRaw_injective

@[simp]
theorem formulaNatCode_inj {n : Nat} {left right : FOFormula n} :
    formulaNatCode left = formulaNatCode right <-> left = right :=
  formulaNatCode_injective.eq_iff

/-- The explicit coding and decoding functions give `FOFormula n` an
`Encodable` instance. -/
instance formulaEncodable (n : Nat) : Encodable (FOFormula n) where
  encode := formulaNatCode
  decode := formulaNatDecode n
  encodek := formulaNatDecode_formulaNatCode

/-! ## Total external enumerations -/

/--
A closed tautology, viewed in any free-variable context.  It supplies an
explicit value when a natural number is not the code of a well-scoped formula.
-/
def defaultFormula (n : Nat) : FOFormula n :=
  .ex (.eq (Fin.last n) (Fin.last n))

/--
A total enumeration of the formulas in one fixed context.  Invalid codes are
sent to `defaultFormula`; this does not turn them into valid syntax codes.
-/
def formulaNatEnumerate (n code : Nat) : FOFormula n :=
  (formulaNatDecode n code).getD (defaultFormula n)

/-- At the displayed code of a formula, total enumeration recovers it. -/
@[simp]
theorem formulaNatEnumerate_formulaNatCode {n : Nat}
    (formula : FOFormula n) :
    formulaNatEnumerate n (formulaNatCode formula) = formula := by
  simp [formulaNatEnumerate]

/-- Every formula of fixed arity occurs in the total enumeration. -/
theorem formulaNatEnumerate_surjective (n : Nat) :
    Function.Surjective (formulaNatEnumerate n) := by
  intro formula
  exact ⟨formulaNatCode formula, formulaNatEnumerate_formulaNatCode formula⟩

/-! ## A single type containing formulas of every arity -/

/-- A formula packaged together with the size of its free-variable context. -/
abbrev PackedFormula : Type := Sigma FOFormula

/-- Pair the arity with the fixed-arity formula code. -/
def packedFormulaNatCode (formula : PackedFormula) : Nat :=
  Nat.pair formula.1 (formulaNatCode formula.2)

/-- Recover both the arity and the formula from a packed code. -/
def packedFormulaNatDecode (code : Nat) : Option PackedFormula :=
  let data := Nat.unpair code
  (formulaNatDecode data.1 data.2).map fun formula => ⟨data.1, formula⟩

/-- Packed decoding is a left inverse, including across distinct arities. -/
@[simp]
theorem packedFormulaNatDecode_packedFormulaNatCode
    (formula : PackedFormula) :
    packedFormulaNatDecode (packedFormulaNatCode formula) = some formula := by
  rcases formula with ⟨n, formula⟩
  unfold packedFormulaNatDecode packedFormulaNatCode
  rw [Nat.unpair_pair]
  dsimp only
  rw [formulaNatDecode_formulaNatCode]
  rfl

/-- The arity/formula package has an injective natural-number code. -/
theorem packedFormulaNatCode_injective :
    Function.Injective packedFormulaNatCode := by
  intro left right h
  have h' := congrArg packedFormulaNatDecode h
  simpa using h'

@[simp]
theorem packedFormulaNatCode_inj {left right : PackedFormula} :
    packedFormulaNatCode left = packedFormulaNatCode right <-> left = right :=
  packedFormulaNatCode_injective.eq_iff

/-- The packed formulas have one explicit injective natural-number coding. -/
instance packedFormulaEncodable : Encodable PackedFormula where
  encode := packedFormulaNatCode
  decode := packedFormulaNatDecode
  encodek := packedFormulaNatDecode_packedFormulaNatCode

/-- A fixed packaged formula, used only as the value at invalid packed codes. -/
def defaultPackedFormula : PackedFormula :=
  ⟨0, defaultFormula 0⟩

/--
A single total enumeration containing formulas of every arity.  Pairing the
arity with the structural formula code prevents formulas in different
contexts from being identified.
-/
def packedFormulaNatEnumerate (code : Nat) : PackedFormula :=
  (packedFormulaNatDecode code).getD defaultPackedFormula

/-- Total packed enumeration recovers every packaged formula at its code. -/
@[simp]
theorem packedFormulaNatEnumerate_packedFormulaNatCode
    (formula : PackedFormula) :
    packedFormulaNatEnumerate (packedFormulaNatCode formula) = formula := by
  simp [packedFormulaNatEnumerate]

/-- Every intrinsically scoped formula, with its arity, occurs in one sequence. -/
theorem packedFormulaNatEnumerate_surjective :
    Function.Surjective packedFormulaNatEnumerate := by
  intro formula
  exact ⟨packedFormulaNatCode formula,
    packedFormulaNatEnumerate_packedFormulaNatCode formula⟩

/-! ## Internal `ZFSet` codes -/

/--
The standard internal omega is a set-sized index set for all formula codes.
Codes that do not decode to a well-scoped formula may simply be skipped.
-/
noncomputable def formulaCodeIndexSet : ZFSet.{u} :=
  Ordinal.omega0.toZFSet

/-- The formula-code index set itself is constructible. -/
theorem formulaCodeIndexSet_mem_L :
    (formulaCodeIndexSet : ZFSet.{u}) ∈ L := by
  simpa only [formulaCodeIndexSet] using (omega_mem_L :
    (Ordinal.omega0.toZFSet : ZFSet.{u}) ∈ L)

/-- The von Neumann natural-number code of a fixed-arity formula. -/
noncomputable def formulaZFCode {n : Nat} (formula : FOFormula n) : ZFSet.{u} :=
  FiniteSequenceZF.natCode (formulaNatCode formula)

/-- Formula `ZFSet` codes are injective. -/
theorem formulaZFCode_injective {n : Nat} :
    Function.Injective (formulaZFCode : FOFormula n -> ZFSet.{u}) :=
  FiniteSequenceZF.natCode_injective.comp formulaNatCode_injective

@[simp]
theorem formulaZFCode_inj {n : Nat} {left right : FOFormula n} :
    (formulaZFCode left : ZFSet.{u}) = formulaZFCode right <-> left = right :=
  formulaZFCode_injective.eq_iff

/-- Every formula code is an element of the standard internal omega. -/
theorem formulaZFCode_mem_omega {n : Nat} (formula : FOFormula n) :
    (formulaZFCode formula : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet := by
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
    (Ordinal.natCast_lt_omega0 (formulaNatCode formula))

/-- Every fixed-arity formula code lies in the common set-sized index set. -/
theorem formulaZFCode_mem_indexSet {n : Nat} (formula : FOFormula n) :
    (formulaZFCode formula : ZFSet.{u}) ∈ formulaCodeIndexSet := by
  exact formulaZFCode_mem_omega formula

/-- Every formula code is constructible. -/
theorem formulaZFCode_mem_L {n : Nat} (formula : FOFormula n) :
    (formulaZFCode formula : ZFSet.{u}) ∈ L := by
  exact FiniteSequenceZF.natCode_mem_L (formulaNatCode formula)

/-- The von Neumann natural-number code of an arity/formula package. -/
noncomputable def packedFormulaZFCode (formula : PackedFormula) : ZFSet.{u} :=
  FiniteSequenceZF.natCode (packedFormulaNatCode formula)

/-- Packed formula `ZFSet` codes are injective, including across arities. -/
theorem packedFormulaZFCode_injective :
    Function.Injective (packedFormulaZFCode : PackedFormula -> ZFSet.{u}) :=
  FiniteSequenceZF.natCode_injective.comp packedFormulaNatCode_injective

@[simp]
theorem packedFormulaZFCode_inj {left right : PackedFormula} :
    (packedFormulaZFCode left : ZFSet.{u}) = packedFormulaZFCode right <->
      left = right :=
  packedFormulaZFCode_injective.eq_iff

/-- Every packed formula code is an element of the standard internal omega. -/
theorem packedFormulaZFCode_mem_omega (formula : PackedFormula) :
    (packedFormulaZFCode formula : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet := by
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
    (Ordinal.natCast_lt_omega0 (packedFormulaNatCode formula))

/-- Every arity/formula package is indexed by the same internal omega. -/
theorem packedFormulaZFCode_mem_indexSet (formula : PackedFormula) :
    (packedFormulaZFCode formula : ZFSet.{u}) ∈ formulaCodeIndexSet := by
  exact packedFormulaZFCode_mem_omega formula

/-- Every packed formula code is constructible. -/
theorem packedFormulaZFCode_mem_L (formula : PackedFormula) :
    (packedFormulaZFCode formula : ZFSet.{u}) ∈ L := by
  exact FiniteSequenceZF.natCode_mem_L (packedFormulaNatCode formula)

end FOFormulaCode

end Constructible
