import OneYTruth.SyntaxCertificates
import OneYTruth.UniformSyntaxSource

/-! The genuine Sigma-one grammar certificate also works with a fixed larger
code bound.  This permits one outer bound to serve every stage of a tower. -/

namespace OneYTruth.GraphStepSyntaxCertificate

open Constructible Constructible.Model FormulaCode
open InternalBoundedIteration UniformSyntaxSource ConstructibleCodeUniverse
open InternalNodes InternalClosure

universe u v w

theorem union_eq_of_bounds {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (B A : LCarrier.{u})
    (hA : A.val = ZFSet.range indexCode)
    (hraw : ∀ (n : Nat) (φ : (language k I).BoundedFormula Empty n),
      formulaCode indexCode φ ∈ B.val)
    (hpacked : ∀ φ : Packed k I, packedCode indexCode φ ∈ B.val) :
    ZFSet.sUnion (InternalIteration.family
      (step SyntaxGrammar.ruleFormula 0
        (fun i => (ConstructibleSyntaxStages.params B A k i).val)) ∅) =
      syntaxCodes (k := k) indexCode :=
  (InternalBoundedIteration.union_eq_L SyntaxGrammar.ruleFormula 0
    (ConstructibleSyntaxStages.params B A k) emptyLCarrier).trans
    (allStages_eq_of_bounds B A hA hraw hpacked)

theorem ordinal_union_eq (κ η : Ordinal.{u}) (hη : η ≤ κ) (k : Nat) :
    ZFSet.sUnion (InternalIteration.family
      (step SyntaxGrammar.ruleFormula 0
        (fun i => (ConstructibleSyntaxStages.params (ordinalBound κ) (ordinalCarrier η) k i).val)) ∅) =
      syntaxCodes (k := k) (ordinalIndexCode (η := η)) := by
  have hi : ∀ i : {ξ : Ordinal.{u} // ξ < η}, ordinalIndexCode i ∈ (ordinalCarrier κ).val :=
    fun i => Ordinal.toZFSet_mem_toZFSet_iff.mpr (lt_of_lt_of_le i.property hη)
  apply union_eq_of_bounds
  · exact (ordinal_range η).symm
  · intro n φ
    exact rawCode_mem hi (toRaw φ)
  · intro φ
    exact pair_mem (natCode_mem (ordinalCarrier κ) φ.1) (rawCode_mem hi (toRaw φ.2))

theorem query_sound {K : Nat} {J : Type w} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (κ η : Ordinal.{u}) (hη : η ≤ κ) (k : Nat)
    (s : Fin 12 → ZFCarrier V)
    (hp : ∀ i : Fin 11, (s i.castSucc).val =
      (ConstructibleSyntaxStages.params (ordinalBound κ) (ordinalCarrier η) k i).val)
    (h : OneYTruth.realize N (SyntaxCertificates.syntaxQuery K J) Empty.elim s) :
    (s 11).val = syntaxCodes (k := k) (ordinalIndexCode (η := η)) := by
  have hh := grammarQueryAt_sound hV N hmem SyntaxGrammar.ruleFormula 0 Fin.castSucc
    4 2 4 (11 : Fin 12) s (hp 2) (hp 4) h
  have hz : (s 4).val = (∅ : ZFSet.{u}) := hp 4
  rw [funext hp, hz, ordinal_union_eq κ η hη k] at hh
  exact hh

theorem realize_query_iff {K : Nat} {J : Type w} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (κ η : Ordinal.{u}) (hη : η ≤ κ) (k : Nat) (s : Fin 12 → ZFCarrier V)
    (hp : ∀ i : Fin 11, (s i.castSucc).val =
      (ConstructibleSyntaxStages.params (ordinalBound κ) (ordinalCarrier η) k i).val) :
    OneYTruth.realize N (SyntaxCertificates.syntaxQuery K J) Empty.elim s ↔
      (s 11).val = syntaxCodes (k := k) (ordinalIndexCode (η := η)) := by
  have hh := realize_grammarQueryAt_iff hV N hmem hCol hSep hpair hUnion hempty
    SyntaxGrammar.ruleFormula 0 Fin.castSucc 4 2 4 (11 : Fin 12) s (hp 2) (hp 4)
  have hz : (s 4).val = (∅ : ZFSet.{u}) := hp 4
  rw [funext hp, hz, ordinal_union_eq κ η hη k] at hh
  exact hh

end OneYTruth.GraphStepSyntaxCertificate
