import OneYTruth.FiniteQuerySemantics

/-! Simultaneous finite representation reflection, reduced to the genuine
local queries. The query soundness/completeness premises must be filled by
the actual Adequate, internal R, and endpoint R formulas; this file does
not claim that those instantiations have already been supplied. -/
namespace OneYTruth.FiniteLabelAssembly
open Constructible OneY.RootIndexed
universe u v

theorem QueryComplete.encode {K : Nat} {J : Type v} {D : Ordinal.{u} → Prop}
    {R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop}
    {G : Diagram} {needs : List TopAtom} {hnv : ∀ d ∈ needs, d.Valid G.size}
    {cut : Nat} {f : Nat → Ordinal.{u}} {β : Ordinal.{u}} {m : Nat}
    {pars : Fin m → ZFCarrier (LStageZF β)} {N : Interpretation K J (ZFCarrier (LStageZF β))}
    {Q : QueryFamily K J G needs (m+G.size)}
    (hC : QueryComplete D R G needs hnv cut f pars N Q)
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (anchor : Fin m)
    (hf : Representation (· < ·) D R G f) (hb : Bounded (· < ·) G.size f β)
    (hn : ∀ d ∈ needs, d.Holds R f β) :
    realize N (diagramFormula.{v,u+1} (labelSlots m G.size anchor) Q) Empty.elim
      (fullAmbient G pars f hb) := by
  let p := fullAmbient G pars f hb
  let v : Fin G.size → Ordinal.{u} := fun i => f i.val
  have hCand : LabelCandidate G cut f pars p v := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i
      exact Fin.append_left pars _ i
    · intro i
      exact (fullAmbient_label G pars f hb i).symm
    · intro i j hij
      exact hf.ordered i.val j.val hij j.isLt
    · intro i
      exact hb i.val i.isLt
    · intro i _
      exact fullAmbient_label G pars f hb i
  have hd : ∀ i, D (v i) := fun i => hf.domain i.val i.isLt
  apply (realize_diagramFormula _ Q N p).mpr
  refine ⟨?_,?_,?_,?_⟩
  · change realize N (OrdinalTupleCertificate.mixedFormula K J G.size) Empty.elim
      (fullAmbient G pars f hb ∘ labelSlots m G.size anchor)
    rw [fullAmbient_slots]
    exact (ambientTuple_facts N hmem D R G f hf hb (pars anchor) needs hnv hn).1
  · intro i
    exact hC.domain p v hCand i (hd i)
  · intro e he
    exact hC.atom p v hCand hd e he (hf.relations e he)
  · intro d hd'
    exact hC.need p v hCand hd d hd' (hn d hd')

/-- The actual map reflects one joint Sigma-one matrix. Metadata and old
prefix labels are fixed; only the remaining labels are existentially
quantified. The conclusion is the literal finite-reflection conclusion. -/
theorem reflect_representation_of_queries
    {K : Nat} {J : Type v} (D : Ordinal.{u} → Prop)
    (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    (G : Diagram) (needs : List TopAtom) (hnv : ∀ d ∈ needs, d.Valid G.size)
    (cut : Nat) (hc : cut < G.size) (f : Nat → Ordinal.{u})
    (hf : Representation (· < ·) D R G f) (β : Ordinal.{u})
    (hb : Bounded (· < ·) G.size f β) (hn : ∀ d ∈ needs, d.Holds R f β)
    (M : Interpretation K J (ZFCarrier (LStageZF (f cut))))
    (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hMmem : M.mem = zfCarrierMem (LStageZF (f cut)))
    (hNmem : N.mem = zfCarrierMem (LStageZF β))
    (hMap : ClosedSigmaOneMap M N (Auxiliary.inclusion (LStageZF_mono (hb cut hc).le)))
    {m : Nat} (pars : Fin m → ZFCarrier (LStageZF (f cut))) (anchor : Fin m)
    (Q : QueryFamily K J G needs (m+G.size))
    (hS : QuerySound D R G needs hnv cut f pars M Q)
    (hC : QueryComplete D R G needs hnv cut f
      (Auxiliary.inclusion (LStageZF_mono (hb cut hc).le) ∘ pars) N Q) :
    ∃ g : Nat → Ordinal.{u}, Representation (· < ·) D R G g ∧
      (∀ i, i < cut → g i = f i) ∧ Bounded (· < ·) G.size g (f cut) ∧
      (∀ d ∈ needs, d.Holds R g (f cut)) := by
  let inc := Auxiliary.inclusion (LStageZF_mono (hb cut hc).le)
  let ambient := fullAmbient G (inc ∘ pars) f hb
  have hA : realize N (diagramFormula.{v,u+1} (labelSlots m G.size anchor) Q) Empty.elim ambient :=
    hC.encode hNmem anchor hf hb hn
  obtain ⟨q,hq,hfix⟩ := reflect_tuple hMap (show m+cut ≤ m+G.size by omega)
    (diagramFormula.{v,u+1} (labelSlots m G.size anchor) Q)
    (diagramFormula_sigma _ Q) (fullFixed hf cut hc pars) ambient
    (fullAmbient_prefix hf cut hc hb pars) hA
  exact hS.decode hMmem hc.le anchor q
    (fixed_full_metadata hf cut hc pars q hfix)
    (fixed_full_label hf cut hc pars q hfix) hq

end OneYTruth.FiniteLabelAssembly
#print axioms OneYTruth.FiniteLabelAssembly.reflect_representation_of_queries
