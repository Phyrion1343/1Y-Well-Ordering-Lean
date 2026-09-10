import OneYTruth.CodedPaths
import OneYTruth.InternalClosure

/-!
# Concrete bounded tag tests and internal existence of atom nodes

The node code has the shape `((arity, rawFormula), assignment)`. The path
left/right/right/left reaches the first tag of the raw-formula sequence.
Testing that tag against the fixed ordinal 5 recognizes exactly the atomic
constructors. Separation is then applied to the already internal full node
set; the result is proved equal to the actual `atomSet`.
-/

namespace OneYTruth.FormulaCode

open Constructible Constructible.FiniteSequenceZF CodedPaths

universe u v

def Raw.tag {I : Type v} : Raw I → Nat
  | .falsum => 0
  | .equal _ _ => 1
  | .mem _ _ => 2
  | .diagonal _ _ _ _ => 3
  | .named _ _ _ => 4
  | .imp _ _ => 5
  | .all _ => 6

def tagPath : List Bool := [false, true, true, false]

theorem follows_formula_tag {I : Type v} (indexCode : I → ZFSet.{u}) (φ : Raw I)
    (arity assignment z : ZFSet.{u}) :
    Follows tagPath (ZFSet.pair (ZFSet.pair arity (rawCode indexCode φ)) assignment) z ↔
      natCode φ.tag = z := by
  cases φ <;> simp [tagPath, rawCode, sequenceCode, listCode, Follows, Raw.tag, eq_comm]

theorem natCode_mem_natCode (n m : Nat) :
    (natCode n : ZFSet.{u}) ∈ natCode m ↔ n < m := by
  rw [natCode, natCode, Ordinal.toZFSet_mem_toZFSet_iff]
  norm_cast

theorem tag_toRaw_lt_five {k : Nat} {I : Type v} {n : Nat}
    (φ : (language k I).BoundedFormula Empty n) :
    (toRaw φ).tag < 5 ↔ SyntaxDiagram.IsAtomic φ := by
  cases φ with
  | falsum => simp [toRaw, Raw.tag, SyntaxDiagram.IsAtomic]
  | equal => simp [toRaw, Raw.tag, SyntaxDiagram.IsAtomic]
  | rel r ts => cases r <;> simp [toRaw, Raw.tag, SyntaxDiagram.IsAtomic]
  | imp => simp [toRaw, Raw.tag, SyntaxDiagram.IsAtomic]
  | all => simp [toRaw, Raw.tag, SyntaxDiagram.IsAtomic]

end OneYTruth.FormulaCode

namespace OneYTruth.AtomicCodeFormula

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula
open Constructible.FiniteSequenceZF FormulaCode CodedPaths SyntaxDiagram InternalClosure

universe u v w

/-- Parameters are the fixed cutoff ordinal 5 and the candidate node code. -/
def atomicFormula : Delta0Formula 2 := pathMemAt tagPath 1 0

theorem satisfies_atomicFormula_code {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (z : ScopedAssignment (k := k) I U) :
    Satisfies ZFMem atomicFormula ![natCode 5, nodeCode indexCode z] ↔ IsAtomic z.1.2 := by
  rw [atomicFormula, satisfies_pathMemAt]
  change (∃ x, Follows tagPath (ZFSet.pair (ZFSet.pair (natCode z.1.1)
    (rawCode indexCode (toRaw z.1.2))) (assignmentCode z.2)) x ∧ x ∈ natCode 5) ↔ _
  simp only [follows_formula_tag, exists_eq_left', natCode_mem_natCode]
  exact tag_toRaw_lt_five z.1.2

def mixedAtomicFormula (k : Nat) (I : Type v) := ofConstructibleDeltaZero k I atomicFormula

theorem mixedAtomicFormula_isDeltaZero (k : Nat) (I : Type v) :
    IsDeltaZero (mixedAtomicFormula k I) :=
  ofConstructibleDeltaZero_isDeltaZero k I atomicFormula

/-- One explicit pure bounded Separation instance internalizes the actual atomic node set.
The full node set must already be an internal set; finite-code closure alone is insufficient. -/
theorem atomSet_mem_of_separation {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {U V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (hSep : SeparationInstance N (mixedAtomicFormula K J))
    (hfive : (natCode 5 : ZFSet.{u}) ∈ V)
    (indexCode : I → ZFSet.{u}) (hnodes : scopedPairs (k := k) U indexCode ∈ V) :
    atomSet (k := k) U indexCode ∈ V := by
  apply filtered_range_mem hV N (mixedAtomicFormula K J) hSep ![⟨natCode 5, hfive⟩]
    (nodeCode (k := k) (U := U) indexCode) (fun z => IsAtomic z.1.2) hnodes
  intro z hz
  rw [mixedAtomicFormula, realize_ofConstructibleDeltaZero_absolute hV N hmem]
  have heq : Constructible.Delta0Formula.val
      (Fin.snoc ![⟨natCode 5, hfive⟩] (⟨nodeCode indexCode z, hz⟩ : ZFCarrier V)) =
      ![natCode 5, nodeCode indexCode z] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact satisfies_atomicFormula_code indexCode z

end OneYTruth.AtomicCodeFormula
