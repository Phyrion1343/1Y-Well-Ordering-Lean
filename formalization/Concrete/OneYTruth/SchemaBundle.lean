import OneYTruth.DirectSchemaCorrect
import OneYTruth.RootSemantics

/-! One bounded check for all closed-stage canonical schemas. The actual
bundle and field bound are explicit; their internal construction is separate. -/

namespace OneYTruth.SchemaBundle

open Constructible Constructible.Delta0Formula
open FirstOrder FirstOrder.Language FormulaCode InternalNodes ExternalTower CodedPaths
open RootSemantics

universe u v

noncomputable def fields {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) : Fin 4 → ZFSet.{u} :=
  ![syntaxCodes (k := s.1) (ordinalIndexCode (η := s.2.val)), assignmentCodes U,
    scopedPairs (k := s.1) U (ordinalIndexCode (η := s.2.val)), truth U s]

def entry (F : Fin 4 → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair (F 0) (ZFSet.pair (F 1) (ZFSet.pair (F 2) (F 3)))

noncomputable def bundle {κ : Ordinal.{u}} (U : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun s : Stage κ => entry (fields U s))

noncomputable def fieldBound {κ : Ordinal.{u}} (U : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun z : Stage κ × Fin 4 => fields U z.1 z.2)

theorem fields_mem_bound {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) (i : Fin 4) :
    fields U s i ∈ @fieldBound κ U := ZFSet.mem_range_self (f := fun z : Stage κ × Fin 4 =>
      fields U z.1 z.2) (s, i)

/-- U,bundle,bound,entry,F,A,nodes,Sat. -/
def body : Delta0Formula 8 :=
  .conj (pathEqAt [false] 3 4)
    (.conj (pathEqAt [true, false] 3 5)
      (.conj (pathEqAt [true, true, false] 3 6)
        (.conj (pathEqAt [true, true, true] 3 7)
          (Delta0Formula.rename ![0, 4, 5, 6, 7] DirectSchema.checkFormula))))

theorem satisfies_body (U B C : ZFSet.{u}) (F : Fin 4 → ZFSet.{u}) (f a n S : ZFSet.{u}) :
    Satisfies ZFMem body ![U, B, C, entry F, f, a, n, S] ↔
      f = F 0 ∧ a = F 1 ∧ n = F 2 ∧ S = F 3 ∧
        Satisfies ZFMem DirectSchema.checkFormula ![U, f, a, n, S] := by
  have ht : (fun i : Fin 5 =>
      (![U, B, C, entry F, f, a, n, S] : Fin 8 → ZFSet.{u}) (![0, 4, 5, 6, 7] i)) =
      ![U, f, a, n, S] := by
    funext i
    fin_cases i <;> rfl
  simp only [body, Satisfies, satisfies_pathEqAt, Delta0Formula.satisfies_rename]
  rw [ht]
  simp [entry, Follows, eq_comm]

attribute [irreducible] body

def formula : Delta0Formula 3 :=
  .boundedAll 1 (.boundedEx 2 (.boundedEx 2 (.boundedEx 2 (.boundedEx 2 body))))

theorem satisfies_formula (U B C : ZFSet.{u}) :
    Satisfies ZFMem formula ![U, B, C] ↔
      ∀ q ∈ B, ∃ f ∈ C, ∃ a ∈ C, ∃ n ∈ C, ∃ S ∈ C,
        Satisfies ZFMem body ![U, B, C, q, f, a, n, S] := by
  simp only [formula, satisfies_boundedAll, Satisfies]
  simp [constructible_snoc_eq, Fin.snoc, Fin.castPred, Fin.castLT, ZFMem]

theorem satisfies_canonical_bundle {κ : Ordinal.{u}} (U : ZFSet.{u}) :
    Satisfies ZFMem formula ![U, @bundle κ U, @fieldBound κ U] ↔
      ∀ s : Stage κ, Satisfies ZFMem DirectSchema.checkFormula
        ![U, fields U s 0, fields U s 1, fields U s 2, fields U s 3] := by
  rw [satisfies_formula]
  constructor
  · intro h s
    obtain ⟨f, _, a, _, n, _, S, _, hh⟩ :=
      h (entry (fields U s)) (ZFSet.mem_range_self (f := fun t : Stage κ => entry (fields U t)) s)
    obtain ⟨rfl, rfl, rfl, rfl, hh⟩ := (satisfies_body _ _ _ _ _ _ _ _).mp hh
    exact hh
  · intro h q hq
    obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hq
    exact ⟨fields U s 0, fields_mem_bound U s 0,
      fields U s 1, fields_mem_bound U s 1,
      fields U s 2, fields_mem_bound U s 2,
      fields U s 3, fields_mem_bound U s 3,
      (satisfies_body _ _ _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl, rfl, h s⟩⟩

theorem satisfies_canonical_bundle_iff {κ : Ordinal.{u}} (U : ZFSet.{u})
    [Nonempty (ZFCarrier U)] :
    Satisfies ZFMem formula ![U, @bundle κ U, @fieldBound κ U] ↔
      ∀ s : Stage κ, InternalClosure.HasSeparation (interpretation U s) ∧
        InternalClosure.HasCollection (interpretation U s) := by
  rw [satisfies_canonical_bundle]
  apply forall_congr'
  intro s
  change Satisfies ZFMem DirectSchema.checkFormula ![U,
    syntaxCodes (k := s.1) (ordinalIndexCode (η := s.2.val)), assignmentCodes U,
    scopedPairs (k := s.1) U (ordinalIndexCode (η := s.2.val)), truth U s] ↔ _
  rw [truth_eq_satisfactionSet, DirectSchema.satisfies_checkFormula,
    DirectSchema.separation_iff_schema ordinalIndexCode ordinalIndexCode_injective,
    DirectSchema.collection_iff_schema ordinalIndexCode ordinalIndexCode_injective]

def mixedFormula (K : Nat) (J : Type v) := ofConstructibleDeltaZero K J formula

theorem mixedFormula_isDeltaZero (K : Nat) (J : Type v) : IsDeltaZero (mixedFormula K J) :=
  ofConstructibleDeltaZero_isDeltaZero _ _ _

theorem realize_iff_adequate {a : Ordinal.{u}}
    (hω : Ordinal.omega0 < a) (hlim : Order.IsSuccLimit a)
    {W : ZFSet.{u}} {K : Nat} {J : Type v} (hW : W.IsTransitive)
    (N : Interpretation K J (ZFCarrier W)) (hNmem : N.mem = zfCarrierMem W)
    (p : Fin 3 → ZFCarrier W)
    (hp : ∀ i, (p i).val = ![LStageZF a, @bundle a (LStageZF a), @fieldBound a (LStageZF a)] i) :
    realize N (mixedFormula K J) Empty.elim p ↔ Adequate a := by
  haveI : Nonempty (ZFCarrier (LStageZF a)) :=
    ⟨⟨∅, empty_mem_LStageZF_of_isSuccLimit hlim⟩⟩
  rw [mixedFormula, realize_ofConstructibleDeltaZero_absolute hW N hNmem]
  have he : Delta0Formula.val p =
      ![LStageZF a, @bundle a (LStageZF a), @fieldBound a (LStageZF a)] := funext hp
  rw [he, satisfies_canonical_bundle_iff]
  constructor
  · intro h
    exact ⟨hω, hlim, fun k η hηa => h (k, ⟨η, hηa⟩)⟩
  · intro h s
    exact h.2.2 s.1 s.2.val s.2.property

end OneYTruth.SchemaBundle

#print axioms OneYTruth.SchemaBundle.realize_iff_adequate
