import OneYTruth.FiniteDiagramMatrix
import OneYTruth.FiniteMetadataLayout

/-! Explicit guarded semantics for the local queries. These interfaces do
not assert reflection or the existence of a representation. The order,
strict bounds, fixed labels, and fixed metadata are supplied before any
relation query is interpreted. -/
namespace OneYTruth.FiniteLabelAssembly
open Constructible OneY.RootIndexed
universe u v

structure LabelCandidate (G : Diagram) (cut : Nat) (f : Nat → Ordinal.{u})
    {β : Ordinal.{u}} {m : Nat} (pars : Fin m → ZFCarrier (LStageZF β))
    (p : Fin (m+G.size) → ZFCarrier (LStageZF β)) (v : Fin G.size → Ordinal.{u}) : Prop where
  parameters : ∀ i, p (Fin.castAdd G.size i) = pars i
  codes : ∀ i, (v i).toZFSet = (p (Fin.natAdd m i)).val
  ordered : StrictMono v
  bounded : ∀ i, v i < β
  fixed : ∀ i : Fin G.size, i.val < cut → (p (Fin.natAdd m i)).val = (f i.val).toZFSet

structure QuerySound {K : Nat} {J : Type v} (D : Ordinal.{u} → Prop)
    (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    (G : Diagram) (needs : List TopAtom) (hnv : ∀ d ∈ needs, d.Valid G.size)
    (cut : Nat) (f : Nat → Ordinal.{u}) {β : Ordinal.{u}} {m : Nat}
    (pars : Fin m → ZFCarrier (LStageZF β)) (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (Q : QueryFamily K J G needs (m+G.size)) : Prop where
  domain : ∀ p v, LabelCandidate G cut f pars p v →
    ∀ i, realize N (Q.domain i) Empty.elim p → D (v i)
  atom : ∀ p v, LabelCandidate G cut f pars p v → (∀ i, D (v i)) →
    ∀ e, ∀ he : e ∈ G.atoms, realize N (Q.atom e) Empty.elim p →
      AtomFinHolds R v e (G.valid e he)
  need : ∀ p v, LabelCandidate G cut f pars p v → (∀ i, D (v i)) →
    ∀ d, ∀ hd : d ∈ needs, realize N (Q.need d) Empty.elim p →
      NeedFinHolds R v β d (hnv d hd)

structure QueryComplete {K : Nat} {J : Type v} (D : Ordinal.{u} → Prop)
    (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    (G : Diagram) (needs : List TopAtom) (hnv : ∀ d ∈ needs, d.Valid G.size)
    (cut : Nat) (f : Nat → Ordinal.{u}) {β : Ordinal.{u}} {m : Nat}
    (pars : Fin m → ZFCarrier (LStageZF β)) (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (Q : QueryFamily K J G needs (m+G.size)) : Prop where
  domain : ∀ p v, LabelCandidate G cut f pars p v →
    ∀ i, D (v i) → realize N (Q.domain i) Empty.elim p
  atom : ∀ p v, LabelCandidate G cut f pars p v → (∀ i, D (v i)) →
    ∀ e, ∀ he : e ∈ G.atoms, AtomFinHolds R v e (G.valid e he) →
      realize N (Q.atom e) Empty.elim p
  need : ∀ p v, LabelCandidate G cut f pars p v → (∀ i, D (v i)) →
    ∀ d, ∀ hd : d ∈ needs, NeedFinHolds R v β d (hnv d hd) →
      realize N (Q.need d) Empty.elim p

/-- Soundness uses the decoded order before domains, and domains before
relations. This is essential for the actual R query's guarded semantics. -/
theorem QuerySound.decode {K : Nat} {J : Type v} {D : Ordinal.{u} → Prop}
    {R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop}
    {G : Diagram} {needs : List TopAtom} {hnv : ∀ d ∈ needs, d.Valid G.size}
    {cut : Nat} {f : Nat → Ordinal.{u}} {β : Ordinal.{u}} {m : Nat}
    {pars : Fin m → ZFCarrier (LStageZF β)} {N : Interpretation K J (ZFCarrier (LStageZF β))}
    {Q : QueryFamily K J G needs (m+G.size)}
    (hS : QuerySound D R G needs hnv cut f pars N Q)
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hc : cut ≤ G.size) (anchor : Fin m)
    (p : Fin (m+G.size) → ZFCarrier (LStageZF β))
    (hp : ∀ i, p (Fin.castAdd G.size i) = pars i)
    (hfix : ∀ i : Fin G.size, i.val < cut → (p (Fin.natAdd m i)).val = (f i.val).toZFSet)
    (h : realize N (diagramFormula.{v,u+1} (labelSlots m G.size anchor) Q) Empty.elim p) :
    ∃ g : Nat → Ordinal.{u}, Representation (· < ·) D R G g ∧
      (∀ i, i < cut → g i = f i) ∧ Bounded (· < ·) G.size g β ∧
      (∀ d ∈ needs, d.Holds R g β) := by
  obtain ⟨ho,hD,hR,hNeeds⟩ := (realize_diagramFormula _ Q N p).mp h
  obtain ⟨v,hv,hm,hb⟩ := (OrdinalTupleCertificate.realize_in_stage N hmem _).mp ho
  have hv' : ∀ i, (v i).toZFSet = (p (Fin.natAdd m i)).val := by
    intro i
    simpa only [Function.comp_apply,labelSlots_label] using hv i
  have hCand : LabelCandidate G cut f pars p v := ⟨hp,hv',hm,hb,hfix⟩
  have hd : ∀ i, D (v i) := fun i => hS.domain p v hCand i (hD i)
  refine ⟨extend v,representation_of_finite D R G v hd hm ?_,
    fixed_of_finite hc v f (fun i hi => (hv' i).trans (hfix i hi)),
    bounded_of_finite v β hb,?_⟩
  · intro e he
    exact hS.atom p v hCand hd e he (hR e he)
  · exact needs_of_finite R v β needs hnv (fun d hd' => hS.need p v hCand hd d hd' (hNeeds d hd'))

end OneYTruth.FiniteLabelAssembly
#print axioms OneYTruth.FiniteLabelAssembly.QuerySound.decode
