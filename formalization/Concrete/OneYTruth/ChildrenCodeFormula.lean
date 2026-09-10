import OneYTruth.ImplicationCodeFormula

/-! The actual quantified-child graph is a boundedly defined subset of the node square. -/

namespace OneYTruth.ChildrenCodeFormula

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open FormulaCode SyntaxDiagram CodedPaths InternalClosure InternalProducts
open FirstOrder FirstOrder.Language ImplicationCodeFormula

universe u v w

abbrev NodePair (k : Nat) (I : Type v) (U : ZFSet.{u}) :=
  ScopedAssignment (k := k) I U × ScopedAssignment (k := k) I U

noncomputable def edgeCode {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (z : NodePair k I U) : ZFSet.{u} :=
  ZFSet.pair (nodeCode indexCode z.1) (nodeCode indexCode z.2)

theorem edgeCode_range {k : Nat} {I : Type v} [Small.{u} I] (U : ZFSet.{u})
    (indexCode : I → ZFSet.{u}) : ZFSet.range (edgeCode (k := k) (U := U) indexCode) =
      pairProduct (scopedPairs (k := k) U indexCode) (scopedPairs (k := k) U indexCode) := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨⟨p, c⟩, h⟩ := ZFSet.mem_range.mp hx
    exact ZFSet.mem_range.mpr ⟨(⟨nodeCode indexCode p, nodeCode_mem_scopedPairs indexCode p⟩,
      ⟨nodeCode indexCode c, nodeCode_mem_scopedPairs indexCode c⟩), h⟩
  · intro hx
    obtain ⟨⟨⟨p, hp⟩, ⟨c, hc⟩⟩, h⟩ := ZFSet.mem_range.mp hx
    obtain ⟨p, rfl⟩ := ZFSet.mem_range.mp hp
    obtain ⟨c, rfl⟩ := ZFSet.mem_range.mp hc
    exact ZFSet.mem_range.mpr ⟨(p, c), h⟩

/-- Parameters: literal tag 6, smaller domain U, candidate edge. -/
def childrenFormula : Delta0Formula 3 :=
  .conj (pathEqAt [false, false, true, true, false] 2 0)
    (.conj (pathsEqualAt [false, false, true, true, true, false] [true, false, true] 2 2)
      (.conj (pathsEqualAt [true, true, true, true] [false, true, true] 2 2)
        (pathMemAt [true, true, true, false] 2 1)))

def Matches {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (z : NodePair k I U) : Prop :=
  match z.1.1.2 with
  | .all φ => formulaCode indexCode φ = formulaCode indexCode z.2.1.2 ∧
    ∃ a : ZFCarrier U, assignmentPayload z.2.2 = ZFSet.pair a.val (assignmentPayload z.1.2)
  | _ => False

theorem satisfies_childrenFormula_codes {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (z : NodePair k I U) :
    Satisfies ZFMem childrenFormula ![natCode 6, U, edgeCode indexCode z] ↔ Matches indexCode z := by
  rcases z with ⟨⟨⟨n, φ⟩, v⟩, c⟩
  cases φ with
  | falsum | equal _ _ | imp _ _ =>
    simp [childrenFormula, Satisfies, satisfies_pathEqAt, satisfies_pathsEqualAt,
      satisfies_pathMemAt, edgeCode, nodeCode, packedCode, formulaCode, toRaw, rawCode,
      sequenceCode, listCode, Follows, natCode_inj, Matches]
  | rel R ts =>
    cases R <;> simp [childrenFormula, Satisfies, satisfies_pathEqAt, satisfies_pathsEqualAt,
      satisfies_pathMemAt, edgeCode, nodeCode, packedCode, formulaCode, toRaw, rawCode,
      sequenceCode, listCode, Follows, natCode_inj, Matches]
  | all φ =>
    simp [childrenFormula, Satisfies, satisfies_pathEqAt, satisfies_pathsEqualAt,
      satisfies_pathMemAt, edgeCode, nodeCode, packedCode, formulaCode, toRaw, rawCode,
      sequenceCode, listCode, assignmentCode_eq_pair, Follows, Matches,
      componentRight_and_leftMem_iff, Subtype.exists]

theorem childrenSet_eq_filtered_pairs {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (indexCode : I → ZFSet.{u}) : childrenSet (k := k) U indexCode =
      ZFSet.range (fun z : {z : NodePair k I U // Matches indexCode z} => edgeCode indexCode z.val) := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨⟨q, a⟩, h⟩ := ZFSet.mem_range.mp hx
    exact ZFSet.mem_range.mpr ⟨⟨(quantifiedParent q, quantifiedChild q a),
      ⟨rfl, a, assignmentPayload_snoc q.2.2 a⟩⟩, h⟩
  · intro hx
    obtain ⟨⟨⟨⟨⟨n, p⟩, v⟩, c⟩, hm⟩, h⟩ := ZFSet.mem_range.mp hx
    cases p with
    | all φ =>
      obtain ⟨hφ, a, ha⟩ := hm
      have hc := nodeCode_eq_of_fields indexCode ⟨⟨n + 1, φ⟩, Fin.snoc v a⟩ c hφ
        (assignmentCode_eq_snoc_of_payload v c.2 a ha).symm
      refine ZFSet.mem_range.mpr ⟨(⟨n, φ, v⟩, a), ?_⟩
      change ZFSet.pair _ (nodeCode indexCode ⟨⟨n + 1, φ⟩, Fin.snoc v a⟩) = x
      rw [hc]
      exact h
    | falsum | equal _ _ | rel _ _ | imp _ _ => exact False.elim hm

def mixedChildrenFormula (k : Nat) (I : Type v) := ofConstructibleDeltaZero k I childrenFormula

theorem mixedChildrenFormula_isDeltaZero (k : Nat) (I : Type v) :
    IsDeltaZero (mixedChildrenFormula k I) :=
  ofConstructibleDeltaZero_isDeltaZero k I childrenFormula

theorem childrenSet_mem_of_separation {k K : Nat} {I : Type v} {J : Type w}
    [Small.{u} I] {U V : ZFSet.{u}} (hV : V.IsTransitive)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = Constructible.zfCarrierMem V)
    (hRepPair : ReplacementInstance N (pairFormula K J))
    (hRepSlice : ReplacementInstance N (mixedSliceGraphFormula K J))
    (hSep : SeparationInstance N (mixedChildrenFormula K J))
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hsix : (natCode 6 : ZFSet.{u}) ∈ V)
    (hU : U ∈ V) (indexCode : I → ZFSet.{u}) (hnodes : scopedPairs (k := k) U indexCode ∈ V) :
    childrenSet (k := k) U indexCode ∈ V := by
  have hsource : ZFSet.range (edgeCode (k := k) (U := U) indexCode) ∈ V := by
    rw [edgeCode_range]
    exact pairProduct_mem hV N hmem hRepPair hRepSlice hpair hUnion hnodes hnodes
  rw [childrenSet_eq_filtered_pairs]
  apply filtered_range_mem hV N (mixedChildrenFormula K J) hSep ![⟨natCode 6, hsix⟩, ⟨U, hU⟩]
    (edgeCode (k := k) (U := U) indexCode) (Matches indexCode) hsource
  intro z hz
  rw [mixedChildrenFormula, realize_ofConstructibleDeltaZero_absolute hV N hmem]
  have heq : Constructible.Delta0Formula.val
      (Fin.snoc ![⟨natCode 6, hsix⟩, ⟨U, hU⟩] (⟨edgeCode indexCode z, hz⟩ : ZFCarrier V)) =
      ![natCode 6, U, edgeCode indexCode z] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact satisfies_childrenFormula_codes indexCode z

end OneYTruth.ChildrenCodeFormula
