import OneYTruth.BoundedEvaluation
import OneYTruth.TarskiCertificate

/-!
# The actual evaluation diagram of all finite formulas

Every diagram component is constructed as a small range of real syntax
and assignments. No purported syntax set or local evaluation graph is
accepted as an unproved field. Locating these sets inside a particular
constructible level remains a separate internal-existence obligation.
-/

namespace OneYTruth.SyntaxDiagram

open FirstOrder FirstOrder.Language Constructible FormulaCode BoundedEvaluation

universe u v

noncomputable def nodeCode {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (w : ScopedAssignment (k := k) I U) : ZFSet.{u} :=
  ZFSet.pair (packedCode indexCode w.1) (assignmentCode w.2)

theorem nodeCode_injective {k : Nat} {I : Type v} {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode) :
    Function.Injective (@nodeCode k I U indexCode) := by
  rintro ⟨φ, v⟩ ⟨ψ, w⟩ h
  obtain ⟨hp, hv⟩ := ZFSet.pair_inj.mp h
  have hφ : φ = ψ := packedCode_injective hi hp
  subst ψ
  have hvw : v = w := assignmentCode_injective hv
  subst w
  rfl

theorem nodeCode_mem_scopedPairs {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (w : ScopedAssignment (k := k) I U) :
    nodeCode indexCode w ∈ scopedPairs (k := k) U indexCode := ZFSet.mem_range_self w

def IsAtomic {k : Nat} {I : Type v} {n : Nat} :
    (language k I).BoundedFormula Empty n → Prop
  | .falsum => True
  | .equal _ _ => True
  | .rel _ _ => True
  | .imp _ _ => False
  | .all _ => False

abbrev AtomicAssignment {k : Nat} (I : Type v) (U : ZFSet.{u}) :=
  {w : ScopedAssignment (k := k) I U // IsAtomic w.1.2}

noncomputable def atomSet {k : Nat} {I : Type v} [Small.{u} I] (U : ZFSet.{u})
    (indexCode : I → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun w : AtomicAssignment (k := k) I U => nodeCode indexCode w.val)

abbrev TrueAtomicAssignment {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (M : Interpretation k I (ZFCarrier U)) :=
  {w : AtomicAssignment (k := k) I U //
    OneYTruth.realize M w.val.1.2 Empty.elim w.val.2}

/-- Only atomic interpretations are consulted; full satisfaction is not an input. -/
noncomputable def trueAtomSet {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (M : Interpretation k I (ZFCarrier U)) : ZFSet.{u} :=
  ZFSet.range (fun w : TrueAtomicAssignment M => nodeCode indexCode w.val.val)

theorem mem_trueAtomSet_iff {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) (w : ScopedAssignment (k := k) I U) :
    nodeCode indexCode w ∈ trueAtomSet indexCode M ↔
      IsAtomic w.1.2 ∧ OneYTruth.realize M w.1.2 Empty.elim w.2 := by
  constructor
  · intro h
    obtain ⟨⟨⟨z, hzA⟩, hzT⟩, heq⟩ := ZFSet.mem_range.mp h
    have hzw : z = w := nodeCode_injective hi heq
    subst z
    exact ⟨hzA, hzT⟩
  · rintro ⟨hA, hT⟩
    exact ZFSet.mem_range_self (f := fun z : TrueAtomicAssignment M =>
      nodeCode indexCode z.val.val) ⟨⟨w, hA⟩, hT⟩

abbrev ImplicationAssignment {k : Nat} (I : Type v) (U : ZFSet.{u}) :=
  Σ n : Nat, ((language k I).BoundedFormula Empty n ×
    (language k I).BoundedFormula Empty n) × (Fin n → ZFCarrier U)

noncomputable def implicationSet {k : Nat} {I : Type v} [Small.{u} I] (U : ZFSet.{u})
    (indexCode : I → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun w : ImplicationAssignment (k := k) I U =>
    Godel.triple (nodeCode indexCode ⟨⟨w.1, .imp w.2.1.1 w.2.1.2⟩, w.2.2⟩)
      (nodeCode indexCode ⟨⟨w.1, w.2.1.1⟩, w.2.2⟩)
      (nodeCode indexCode ⟨⟨w.1, w.2.1.2⟩, w.2.2⟩))

abbrev QuantifiedAssignment {k : Nat} (I : Type v) (U : ZFSet.{u}) :=
  Σ n : Nat, (language k I).BoundedFormula Empty (n + 1) × (Fin n → ZFCarrier U)

def quantifiedParent {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (w : QuantifiedAssignment (k := k) I U) : ScopedAssignment (k := k) I U :=
  ⟨⟨w.1, .all w.2.1⟩, w.2.2⟩

def quantifiedChild {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (w : QuantifiedAssignment (k := k) I U) (a : ZFCarrier U) :
    ScopedAssignment (k := k) I U := ⟨⟨w.1 + 1, w.2.1⟩, Fin.snoc w.2.2 a⟩

theorem quantifiedParentCode_injective {k : Nat} {I : Type v} {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode) :
    Function.Injective (fun w : QuantifiedAssignment (k := k) I U =>
      nodeCode indexCode (quantifiedParent w)) := by
  rintro ⟨n, φ, v⟩ ⟨m, ψ, w⟩ h
  obtain ⟨hp, hv⟩ := ZFSet.pair_inj.mp h
  have hpacked := packedCode_injective hi hp
  have hnm : n = m := congrArg Sigma.fst hpacked
  subst m
  have hall : (.all φ : (language k I).BoundedFormula Empty n) = .all ψ :=
    eq_of_heq (Sigma.mk.inj_iff.mp hpacked).2
  have hφ : φ = ψ := BoundedFormula.all.inj hall
  subst ψ
  have hvw : v = w := assignmentCode_injective hv
  subst w
  rfl

noncomputable def quantifiedSet {k : Nat} {I : Type v} [Small.{u} I] (U : ZFSet.{u})
    (indexCode : I → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun w : QuantifiedAssignment (k := k) I U =>
    nodeCode indexCode (quantifiedParent w))

noncomputable def childrenSet {k : Nat} {I : Type v} [Small.{u} I] (U : ZFSet.{u})
    (indexCode : I → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun w : QuantifiedAssignment (k := k) I U × ZFCarrier U =>
    ZFSet.pair (nodeCode indexCode (quantifiedParent w.1))
      (nodeCode indexCode (quantifiedChild w.1 w.2)))

/-- The diagram contains real syntactic cases and the actual atomic truth table. -/
noncomputable def diagram {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (M : Interpretation k I (ZFCarrier U)) : Diagram.{u} where
  nodes := scopedPairs (k := k) U indexCode
  atoms := atomSet (k := k) U indexCode
  trueAtoms := trueAtomSet indexCode M
  implications := implicationSet (k := k) U indexCode
  quantified := quantifiedSet (k := k) U indexCode
  children := childrenSet (k := k) U indexCode

/-- The coded children of one quantified node are exactly its individual assignments. -/
theorem all_children_iff {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode) (S : ZFSet.{u})
    (w : QuantifiedAssignment (k := k) I U) :
    (∀ q ∈ scopedPairs (k := k) U indexCode,
      ZFSet.pair (nodeCode indexCode (quantifiedParent w)) q ∈ childrenSet (k := k) U indexCode → q ∈ S) ↔
    ∀ a : ZFCarrier U, nodeCode indexCode (quantifiedChild w a) ∈ S := by
  constructor
  · intro h a
    apply h _ (nodeCode_mem_scopedPairs indexCode _)
    exact ZFSet.mem_range_self (f := fun z : QuantifiedAssignment (k := k) I U × ZFCarrier U =>
      ZFSet.pair (nodeCode indexCode (quantifiedParent z.1))
        (nodeCode indexCode (quantifiedChild z.1 z.2))) (w, a)
  · intro h q _ hq
    obtain ⟨⟨z, a⟩, hz⟩ := ZFSet.mem_range.mp hq
    obtain ⟨hp, hc⟩ := ZFSet.pair_inj.mp hz
    have hzw : z = w := quantifiedParentCode_injective hi hp
    subst z
    exact hc ▸ h a

end OneYTruth.SyntaxDiagram
