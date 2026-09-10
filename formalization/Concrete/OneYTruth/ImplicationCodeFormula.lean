import OneYTruth.InternalNodes
import OneYTruth.AssignmentFields
import OneYTruth.AtomicCodeFormula

/-! Canonical implication edges are recognized by fixed bounded code paths. -/

namespace OneYTruth.ImplicationCodeFormula

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open FormulaCode SyntaxDiagram CodedPaths InternalClosure InternalProducts
open FirstOrder FirstOrder.Language

universe u v w

abbrev NodeTriple (k : Nat) (I : Type v) (U : ZFSet.{u}) :=
  ScopedAssignment (k := k) I U × ScopedAssignment (k := k) I U × ScopedAssignment (k := k) I U

noncomputable def tripleCode {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (z : NodeTriple k I U) : ZFSet.{u} :=
  Godel.triple (nodeCode indexCode z.1) (nodeCode indexCode z.2.1) (nodeCode indexCode z.2.2)

theorem tripleCode_range {k : Nat} {I : Type v} [Small.{u} I] (U : ZFSet.{u})
    (indexCode : I → ZFSet.{u}) : ZFSet.range (tripleCode (k := k) (U := U) indexCode) =
      pairProduct (scopedPairs (k := k) U indexCode)
        (pairProduct (scopedPairs (k := k) U indexCode) (scopedPairs (k := k) U indexCode)) := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨⟨p, a, b⟩, h⟩ := ZFSet.mem_range.mp hx
    exact ZFSet.mem_range.mpr ⟨(⟨nodeCode indexCode p, nodeCode_mem_scopedPairs indexCode p⟩,
      ⟨ZFSet.pair (nodeCode indexCode a) (nodeCode indexCode b), ZFSet.mem_range.mpr
        ⟨(⟨_, nodeCode_mem_scopedPairs indexCode a⟩,
          ⟨_, nodeCode_mem_scopedPairs indexCode b⟩), rfl⟩⟩), h⟩
  · intro hx
    obtain ⟨⟨⟨p, hp⟩, ⟨ab, hab⟩⟩, h⟩ := ZFSet.mem_range.mp hx
    obtain ⟨p, rfl⟩ := ZFSet.mem_range.mp hp
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩ := ZFSet.mem_range.mp hab
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp ha
    obtain ⟨b, rfl⟩ := ZFSet.mem_range.mp hb
    exact ZFSet.mem_range.mpr ⟨(p, a, b), h⟩

/-- The free parameters are the literal tag 5 and a candidate node triple. -/
def implicationFormula : Delta0Formula 2 :=
  .conj (pathEqAt [false, false, true, true, false] 1 0)
  (.conj (pathsEqualAt [false, false, true, true, true, false] [true, false, false, true] 1 1)
  (.conj (pathsEqualAt [false, false, true, true, true, true, false] [true, true, false, true] 1 1)
  (.conj (pathsEqualAt [false, true] [true, false, true] 1 1)
    (pathsEqualAt [false, true] [true, true, true] 1 1))))

def Matches {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (z : NodeTriple k I U) : Prop :=
  match z.1.1.2 with
  | .imp φ ψ =>
    formulaCode indexCode φ = formulaCode indexCode z.2.1.1.2 ∧
    formulaCode indexCode ψ = formulaCode indexCode z.2.2.1.2 ∧
    assignmentCode z.1.2 = assignmentCode z.2.1.2 ∧
    assignmentCode z.1.2 = assignmentCode z.2.2.2
  | _ => False

theorem satisfies_implicationFormula_codes {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (z : NodeTriple k I U) :
    Satisfies ZFMem implicationFormula ![natCode 5, tripleCode indexCode z] ↔ Matches indexCode z := by
  rcases z with ⟨⟨⟨n, φ⟩, v⟩, a, b⟩
  cases φ <;> simp [implicationFormula, Satisfies, satisfies_pathEqAt,
    satisfies_pathsEqualAt, tripleCode, nodeCode, Godel.triple, packedCode,
    formulaCode, toRaw, rawCode, sequenceCode, listCode, Follows, natCode_inj, Matches]
  rename_i l R ts
  cases R <;> simp [toRaw, rawCode, sequenceCode, listCode, natCode_inj]

theorem nodeCode_eq_of_fields {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (a b : ScopedAssignment (k := k) I U)
    (hf : formulaCode indexCode a.1.2 = formulaCode indexCode b.1.2)
    (hv : assignmentCode a.2 = assignmentCode b.2) : nodeCode indexCode a = nodeCode indexCode b := by
  have hn := assignmentCode_arity_eq hv
  exact congrArg₂ ZFSet.pair (congrArg₂ ZFSet.pair (congrArg natCode hn) hf) hv

theorem implicationSet_eq_filtered_triples {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (indexCode : I → ZFSet.{u}) :
    implicationSet (k := k) U indexCode = ZFSet.range
      (fun z : {z : NodeTriple k I U // Matches indexCode z} => tripleCode indexCode z.val) := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨⟨n, ⟨φ, ψ⟩, v⟩, h⟩ := ZFSet.mem_range.mp hx
    exact ZFSet.mem_range.mpr ⟨⟨(⟨⟨n, .imp φ ψ⟩, v⟩, ⟨⟨n, φ⟩, v⟩, ⟨⟨n, ψ⟩, v⟩),
      ⟨rfl, rfl, rfl, rfl⟩⟩, h⟩
  · intro hx
    obtain ⟨⟨⟨⟨⟨n, p⟩, v⟩, a, b⟩, hmatch⟩, h⟩ := ZFSet.mem_range.mp hx
    cases p with
    | imp φ ψ =>
      obtain ⟨hφ, hψ, ha, hb⟩ := hmatch
      have hca := nodeCode_eq_of_fields indexCode ⟨⟨n, φ⟩, v⟩ a hφ ha
      have hcb := nodeCode_eq_of_fields indexCode ⟨⟨n, ψ⟩, v⟩ b hψ hb
      refine ZFSet.mem_range.mpr ⟨⟨n, (φ, ψ), v⟩, ?_⟩
      rw [hca, hcb]
      exact h
    | falsum | equal _ _ | rel _ _ | all _ => exact False.elim hmatch

def mixedImplicationFormula (k : Nat) (I : Type v) :=
  ofConstructibleDeltaZero k I implicationFormula

theorem mixedImplicationFormula_isDeltaZero (k : Nat) (I : Type v) :
    IsDeltaZero (mixedImplicationFormula k I) :=
  ofConstructibleDeltaZero_isDeltaZero k I implicationFormula

theorem implicationSet_mem_of_separation {k K : Nat} {I : Type v} {J : Type w}
    [Small.{u} I] {U V : ZFSet.{u}} (hV : V.IsTransitive)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = Constructible.zfCarrierMem V)
    (hRepPair : ReplacementInstance N (pairFormula K J))
    (hRepSlice : ReplacementInstance N (mixedSliceGraphFormula K J))
    (hSep : SeparationInstance N (mixedImplicationFormula K J))
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hfive : (natCode 5 : ZFSet.{u}) ∈ V)
    (indexCode : I → ZFSet.{u}) (hnodes : scopedPairs (k := k) U indexCode ∈ V) :
    implicationSet (k := k) U indexCode ∈ V := by
  have hsource : ZFSet.range (tripleCode (k := k) (U := U) indexCode) ∈ V := by
    rw [tripleCode_range]
    exact pairProduct_mem hV N hmem hRepPair hRepSlice hpair hUnion hnodes
      (pairProduct_mem hV N hmem hRepPair hRepSlice hpair hUnion hnodes hnodes)
  rw [implicationSet_eq_filtered_triples]
  apply filtered_range_mem hV N (mixedImplicationFormula K J) hSep ![⟨natCode 5, hfive⟩]
    (tripleCode (k := k) (U := U) indexCode) (Matches indexCode) hsource
  intro z hz
  rw [mixedImplicationFormula, realize_ofConstructibleDeltaZero_absolute hV N hmem]
  have heq : Constructible.Delta0Formula.val
      (Fin.snoc ![⟨natCode 5, hfive⟩] (⟨tripleCode indexCode z, hz⟩ : ZFCarrier V)) =
      ![natCode 5, tripleCode indexCode z] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact satisfies_implicationFormula_codes indexCode z

end OneYTruth.ImplicationCodeFormula
