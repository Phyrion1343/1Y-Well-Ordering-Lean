import OneYTruth.AtomicCodeFormula

/-!
# The actual quantified-node set is a bounded separation of all nodes

Among valid raw constructors, tag 6 is the only tag not below 6. A second
explicit pure bounded Separation instance therefore constructs the actual
`quantifiedSet`, without assuming it internal as a separate closure field.
-/

namespace OneYTruth.SyntaxDiagram

open FirstOrder FirstOrder.Language Constructible

universe u v

def IsQuantified {k : Nat} {I : Type v} {n : Nat} :
    (language k I).BoundedFormula Empty n → Prop
  | .all _ => True
  | _ => False

theorem exists_quantifiedParent {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (z : ScopedAssignment (k := k) I U) (hz : IsQuantified z.1.2) :
    ∃ q : QuantifiedAssignment (k := k) I U, quantifiedParent q = z := by
  obtain ⟨⟨n, φ⟩, v⟩ := z
  cases φ with
  | falsum => exact False.elim hz
  | equal => exact False.elim hz
  | rel => exact False.elim hz
  | imp => exact False.elim hz
  | all φ => exact ⟨⟨_, φ, v⟩, rfl⟩

theorem quantifiedSet_eq_filtered_range {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (indexCode : I → ZFSet.{u}) :
    quantifiedSet (k := k) U indexCode =
      ZFSet.range (fun z : {z : ScopedAssignment (k := k) I U // IsQuantified z.1.2} =>
        nodeCode indexCode z.val) := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨q, hq⟩ := ZFSet.mem_range.mp hx
    exact ZFSet.mem_range.mpr ⟨⟨quantifiedParent q, trivial⟩, hq⟩
  · intro hx
    obtain ⟨⟨z, hz⟩, heq⟩ := ZFSet.mem_range.mp hx
    obtain ⟨q, hq⟩ := exists_quantifiedParent z hz
    subst z
    exact ZFSet.mem_range.mpr ⟨q, heq⟩

end OneYTruth.SyntaxDiagram

namespace OneYTruth.QuantifiedCodeFormula

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula
open Constructible.FiniteSequenceZF FormulaCode CodedPaths SyntaxDiagram InternalClosure

universe u v w

def quantifiedFormula : Delta0Formula 2 := .neg AtomicCodeFormula.atomicFormula

theorem tag_toRaw_not_lt_six {k : Nat} {I : Type v} {n : Nat}
    (φ : (language k I).BoundedFormula Empty n) :
    ¬ (toRaw φ).tag < 6 ↔ IsQuantified φ := by
  cases φ with
  | falsum => simp [toRaw, Raw.tag, IsQuantified]
  | equal => simp [toRaw, Raw.tag, IsQuantified]
  | rel r ts => cases r <;> simp [toRaw, Raw.tag, IsQuantified]
  | imp => simp [toRaw, Raw.tag, IsQuantified]
  | all => simp [toRaw, Raw.tag, IsQuantified]

theorem satisfies_quantifiedFormula_code {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (z : ScopedAssignment (k := k) I U) :
    Satisfies ZFMem quantifiedFormula ![natCode 6, nodeCode indexCode z] ↔ IsQuantified z.1.2 := by
  rw [quantifiedFormula, Satisfies, AtomicCodeFormula.atomicFormula, satisfies_pathMemAt]
  change (¬ ∃ x, Follows tagPath (ZFSet.pair (ZFSet.pair (natCode z.1.1)
    (rawCode indexCode (toRaw z.1.2))) (assignmentCode z.2)) x ∧ x ∈ natCode 6) ↔ _
  simp only [follows_formula_tag, exists_eq_left', natCode_mem_natCode]
  exact tag_toRaw_not_lt_six z.1.2

def mixedQuantifiedFormula (k : Nat) (I : Type v) :=
  ofConstructibleDeltaZero k I quantifiedFormula

theorem mixedQuantifiedFormula_isDeltaZero (k : Nat) (I : Type v) :
    IsDeltaZero (mixedQuantifiedFormula k I) :=
  ofConstructibleDeltaZero_isDeltaZero k I quantifiedFormula

theorem quantifiedSet_mem_of_separation {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {U V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (hSep : SeparationInstance N (mixedQuantifiedFormula K J))
    (hsix : (natCode 6 : ZFSet.{u}) ∈ V)
    (indexCode : I → ZFSet.{u}) (hnodes : scopedPairs (k := k) U indexCode ∈ V) :
    quantifiedSet (k := k) U indexCode ∈ V := by
  rw [quantifiedSet_eq_filtered_range]
  apply filtered_range_mem hV N (mixedQuantifiedFormula K J) hSep ![⟨natCode 6, hsix⟩]
    (nodeCode (k := k) (U := U) indexCode) (fun z => IsQuantified z.1.2) hnodes
  intro z hz
  rw [mixedQuantifiedFormula, realize_ofConstructibleDeltaZero_absolute hV N hmem]
  have heq : Constructible.Delta0Formula.val
      (Fin.snoc ![⟨natCode 6, hsix⟩] (⟨nodeCode indexCode z, hz⟩ : ZFCarrier V)) =
      ![natCode 6, nodeCode indexCode z] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact satisfies_quantifiedFormula_code indexCode z

end OneYTruth.QuantifiedCodeFormula
