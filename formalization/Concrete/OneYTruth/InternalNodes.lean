import OneYTruth.InternalProducts
import OneYTruth.PathEquality
import OneYTruth.SyntaxDiagram

/-!
# Internal canonical node sets from internal syntax and assignment sets

The complete scoped node set is obtained by an actual bounded Separation
instance on a Cartesian product. The two complete source sets, rather than
merely their individual members, are hypotheses of the theorem.
-/

namespace OneYTruth.InternalNodes

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula
open Constructible.FiniteSequenceZF FormulaCode SyntaxDiagram InternalClosure InternalProducts
open CodedPaths

universe u v w

abbrev PackedAssignment (U : ZFSet.{u}) := Σ n : Nat, Fin n → ZFCarrier U

noncomputable def syntaxCodes {k : Nat} {I : Type v} [Small.{u} I]
    (indexCode : I → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (packedCode (k := k) indexCode)

noncomputable def assignmentCodes (U : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun a : PackedAssignment U => assignmentCode a.2)

noncomputable def crossCode {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (z : Packed k I × PackedAssignment U) : ZFSet.{u} :=
  ZFSet.pair (packedCode indexCode z.1) (assignmentCode z.2.2)

theorem crossCode_range {k : Nat} {I : Type v} [Small.{u} I] (U : ZFSet.{u})
    (indexCode : I → ZFSet.{u}) :
    ZFSet.range (crossCode (k := k) (U := U) indexCode) =
      pairProduct (syntaxCodes (k := k) indexCode) (assignmentCodes U) := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨⟨p, a⟩, h⟩ := ZFSet.mem_range.mp hx
    exact ZFSet.mem_range.mpr ⟨(⟨packedCode indexCode p, ZFSet.mem_range_self p⟩,
      ⟨assignmentCode a.2, ZFSet.mem_range_self a⟩), h⟩
  · intro hx
    obtain ⟨⟨⟨p, hp⟩, ⟨a, ha⟩⟩, h⟩ := ZFSet.mem_range.mp hx
    obtain ⟨φ, rfl⟩ := ZFSet.mem_range.mp hp
    obtain ⟨v, rfl⟩ := ZFSet.mem_range.mp ha
    exact ZFSet.mem_range.mpr ⟨(φ, v), h⟩

/-- Both literal arity fields of a candidate `(packedFormula,assignment)` agree. -/
def matchingArityFormula : Delta0Formula 1 := pathsEqualAt [false, false] [true, false] 0 0

theorem satisfies_matchingArityFormula {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (z : Packed k I × PackedAssignment U) :
    Satisfies ZFMem matchingArityFormula ![crossCode indexCode z] ↔ z.1.1 = z.2.1 := by
  rw [matchingArityFormula, satisfies_pathsEqualAt]
  simp [crossCode, packedCode, assignmentCode, sequenceCode, Follows,
    natCode_inj]

theorem scopedPairs_eq_filtered_crossCode {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (indexCode : I → ZFSet.{u}) :
    scopedPairs (k := k) U indexCode = ZFSet.range
      (fun z : {z : Packed k I × PackedAssignment U // z.1.1 = z.2.1} =>
        crossCode indexCode z.val) := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨⟨⟨n, φ⟩, a⟩, h⟩ := ZFSet.mem_range.mp hx
    exact ZFSet.mem_range.mpr ⟨⟨(⟨n, φ⟩, ⟨n, a⟩), rfl⟩, h⟩
  · intro hx
    obtain ⟨⟨⟨⟨n, φ⟩, ⟨m, a⟩⟩, heq⟩, h⟩ := ZFSet.mem_range.mp hx
    change n = m at heq
    subst m
    exact ZFSet.mem_range.mpr ⟨⟨⟨n, φ⟩, a⟩, h⟩

def mixedMatchingArityFormula (k : Nat) (I : Type v) :=
  ofConstructibleDeltaZero k I matchingArityFormula

theorem mixedMatchingArityFormula_isDeltaZero (k : Nat) (I : Type v) :
    IsDeltaZero (mixedMatchingArityFormula k I) :=
  ofConstructibleDeltaZero_isDeltaZero k I matchingArityFormula

theorem scopedPairs_mem_of_internal_sources {k K : Nat} {I : Type v} {J : Type w}
    [Small.{u} I] {U V : ZFSet.{u}} (hV : V.IsTransitive)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = Constructible.zfCarrierMem V)
    (hRepPair : ReplacementInstance N (pairFormula K J))
    (hRepSlice : ReplacementInstance N (mixedSliceGraphFormula K J))
    (hSep : SeparationInstance N (mixedMatchingArityFormula K J))
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    (indexCode : I → ZFSet.{u}) (hSyntax : syntaxCodes (k := k) indexCode ∈ V)
    (hAssignments : assignmentCodes U ∈ V) : scopedPairs (k := k) U indexCode ∈ V := by
  have hsource : ZFSet.range (crossCode (k := k) (U := U) indexCode) ∈ V := by
    rw [crossCode_range]
    exact pairProduct_mem hV N hmem hRepPair hRepSlice hpair hUnion hSyntax hAssignments
  rw [scopedPairs_eq_filtered_crossCode]
  apply filtered_range_mem hV N (mixedMatchingArityFormula K J) hSep ![]
    (crossCode (k := k) (U := U) indexCode) (fun z => z.1.1 = z.2.1) hsource
  intro z hz
  rw [mixedMatchingArityFormula, realize_ofConstructibleDeltaZero_absolute hV N hmem]
  have heq : Constructible.Delta0Formula.val
      (Fin.snoc ![] (⟨crossCode indexCode z, hz⟩ : ZFCarrier V)) = ![crossCode indexCode z] := by
    funext i
    fin_cases i
    rfl
  rw [heq]
  exact satisfies_matchingArityFormula indexCode z

end OneYTruth.InternalNodes
