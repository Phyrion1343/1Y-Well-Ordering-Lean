import OneYTruth.FiniteReflectionAssembly

/-! The actual canonical R supplies the precise closed-scope map used by
finite witness reflection. Local query semantics remain explicit here. -/
namespace OneYTruth.RootSemantics
open Constructible ExternalTower OneY.RootIndexed FiniteLabelAssembly
universe u

theorem Adequate.carrier_nonempty {a : Ordinal.{u}} (ha : Adequate a) :
    Nonempty (ZFCarrier (LStageZF a)) :=
  ⟨⟨∅,empty_mem_LStageZF_of_isSuccLimit ha.2.1⟩⟩

theorem R.closedMap {K : Nat} {θ a b : Ordinal.{u}}
    (ha : Adequate a) (hθa : θ ≤ a) (hab : a < b) (h : R K θ a b) :
    ClosedSigmaOneMap (interpretation (LStageZF a) (K,⟨θ,hθa⟩))
      (interpretation (LStageZF b) (K,⟨θ,hθa.trans hab.le⟩))
      (Auxiliary.inclusion (LStageZF_mono hab.le)) := by
  letI : Nonempty (ZFCarrier (LStageZF a)) := ha.carrier_nonempty
  obtain ⟨_,_,hf⟩ := h
  exact (sigmaOneMap_iff_closed _ _ _).mp hf

/-- A usable concrete exit from actual R and independently verified local
query semantics. No arbitrary structures, map, membership interpretation,
or candidate representation are premises. -/
theorem R.reflect_diagram_of_queries
    (G : Diagram) (needs : List TopAtom) (hnv : ∀ d ∈ needs, d.Valid G.size)
    (cut : Nat) (hc : cut < G.size) (f : Nat → Ordinal.{u})
    (hf : Representation (· < ·) Adequate R G f) (β : Ordinal.{u})
    (hb : Bounded (· < ·) G.size f β) (hn : ∀ d ∈ needs, d.Holds R f β)
    (K : Nat) (θ : Ordinal.{u}) (hθ : θ ≤ f cut) (hR : R K θ (f cut) β)
    {m : Nat} (pars : Fin m → ZFCarrier (LStageZF (f cut))) (anchor : Fin m)
    (Q : QueryFamily K {ξ : Ordinal.{u} // ξ < θ} G needs (m+G.size))
    (hS : QuerySound Adequate R G needs hnv cut f pars
      (interpretation (LStageZF (f cut)) (K,⟨θ,hθ⟩)) Q)
    (hC : QueryComplete Adequate R G needs hnv cut f
      (Auxiliary.inclusion (LStageZF_mono (hb cut hc).le) ∘ pars)
      (interpretation (LStageZF β) (K,⟨θ,hθ.trans (hb cut hc).le⟩)) Q) :
    ∃ g : Nat → Ordinal.{u}, Representation (· < ·) Adequate R G g ∧
      (∀ i, i < cut → g i = f i) ∧ Bounded (· < ·) G.size g (f cut) ∧
      (∀ d ∈ needs, d.Holds R g (f cut)) := by
  exact reflect_representation_of_queries Adequate R G needs hnv cut hc f hf β hb hn
    (interpretation (LStageZF (f cut)) (K,⟨θ,hθ⟩))
    (interpretation (LStageZF β) (K,⟨θ,hθ.trans (hb cut hc).le⟩)) rfl rfl
    (hR.closedMap (hf.domain cut hc) hθ (hb cut hc)) pars anchor Q hS hC

end OneYTruth.RootSemantics
#print axioms OneYTruth.RootSemantics.R.closedMap
#print axioms OneYTruth.RootSemantics.R.reflect_diagram_of_queries
