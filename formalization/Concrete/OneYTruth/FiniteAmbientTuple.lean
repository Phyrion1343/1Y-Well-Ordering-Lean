import OneYTruth.FiniteTupleDecoding

/-! The original bounded representation supplies literal internal witnesses.
The displayed top ordinal remains external. -/
namespace OneYTruth.FiniteLabelAssembly
open Constructible OneY.RootIndexed
universe u v

noncomputable def ordinalCarrier {β : Ordinal.{u}} (a : Ordinal.{u}) (ha : a < β) :
    ZFCarrier (LStageZF β) :=
  ⟨a.toZFSet, ordinal_toZFSet_mem_LStageZF_of_lt ha⟩

noncomputable def ambientTuple {β : Ordinal.{u}} (G : Diagram) (f : Nat → Ordinal.{u})
    (hb : Bounded (· < ·) G.size f β) (anchor : ZFCarrier (LStageZF β)) :
    Fin (G.size+1) → ZFCarrier (LStageZF β) :=
  Fin.snoc (fun i : Fin G.size => ordinalCarrier (f i.val) (hb i.val i.isLt)) anchor

@[simp] theorem ambientTuple_code {β : Ordinal.{u}} (G : Diagram) (f : Nat → Ordinal.{u})
    (hb : Bounded (· < ·) G.size f β) (anchor : ZFCarrier (LStageZF β)) (i : Fin G.size) :
    (ambientTuple G f hb anchor i.castSucc).val = (f i.val).toZFSet := by
  simp [ambientTuple, ordinalCarrier]

noncomputable def fixedPrefix {G : Diagram} {D : Ordinal.{u} → Prop}
    {R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop}
    {f : Nat → Ordinal.{u}} (hf : Representation (· < ·) D R G f)
    (cut : Nat) (hc : cut < G.size) : Fin cut → ZFCarrier (LStageZF (f cut)) :=
  fun i => ordinalCarrier (f i.val) (hf.ordered i.val cut i.isLt hc)

@[simp] theorem fixedPrefix_code {G : Diagram} {D : Ordinal.{u} → Prop}
    {R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop}
    {f : Nat → Ordinal.{u}} (hf : Representation (· < ·) D R G f)
    (cut : Nat) (hc : cut < G.size) (i : Fin cut) :
    (fixedPrefix hf cut hc i).val = (f i.val).toZFSet := rfl

/-- All ambient finite facts are consequences of the old representation,
its strict bound, and the actual demands. -/
theorem ambientTuple_facts {K : Nat} {J : Type v} {β : Ordinal.{u}}
    (N : Interpretation K J (ZFCarrier (LStageZF β))) (hmem : N.mem = zfCarrierMem (LStageZF β))
    (D : Ordinal.{u} → Prop) (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    (G : Diagram) (f : Nat → Ordinal.{u}) (hf : Representation (· < ·) D R G f)
    (hb : Bounded (· < ·) G.size f β) (anchor : ZFCarrier (LStageZF β))
    (needs : List TopAtom) (hnv : ∀ d ∈ needs, d.Valid G.size)
    (hn : ∀ d ∈ needs, d.Holds R f β) :
    let p := ambientTuple G f hb anchor
    realize N (OrdinalTupleCertificate.mixedFormula K J G.size) Empty.elim p ∧
      (∀ i : Fin G.size, CodeDomain D (p i.castSucc).val) ∧
      (∀ e, ∀ he : e ∈ G.atoms,
        CodeAtomHolds R (fun i : Fin G.size => (p i.castSucc).val) e (G.valid e he)) ∧
      (∀ d, ∀ hd : d ∈ needs,
        CodeNeedHolds R (fun i : Fin G.size => (p i.castSucc).val) β d (hnv d hd)) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · apply (OrdinalTupleCertificate.realize_in_stage N hmem _).mpr
    refine ⟨fun i => f i.val, fun i => (ambientTuple_code G f hb anchor i).symm, ?_, ?_⟩
    · intro i j hij
      exact hf.ordered i.val j.val hij j.isLt
    · intro i
      exact hb i.val i.isLt
  · intro i
    rw [ambientTuple_code]
    exact (codeDomain_codes D _).mpr (hf.domain i.val i.isLt)
  · intro e he
    unfold CodeAtomHolds
    simp only [ambientTuple_code]
    exact (codeRelation_codes R _ _ _ _).mpr (hf.relations e he)
  · intro d hd
    unfold CodeNeedHolds
    simp only [ambientTuple_code]
    exact (codeTopRelation_codes R _ _ _ _).mpr (hn d hd)

end OneYTruth.FiniteLabelAssembly
#print axioms OneYTruth.FiniteLabelAssembly.ambientTuple_facts
