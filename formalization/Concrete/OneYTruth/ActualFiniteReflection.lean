import OneYTruth.ActualDiagramQueries
import OneYTruth.ActualReflectionMap

/-! Finite reflection for the actual canonical mixed-truth relations.
Every local query and every fixed metadata value is supplied by a proved
construction. No finite-reflection or well-foundedness assumption occurs. -/

namespace OneYTruth.RootSemantics

open Constructible OneY.RootIndexed FiniteLabelAssembly ActualDiagramQueries

universe u

theorem actual_finiteReflection :
    FiniteReflection (α := Ordinal.{u}) (· < ·) Adequate R := by
  intro G cut K θ β f needs hc hf hβ hb hR hnv hAdm hn
  have ha : Adequate (f cut) := hf.domain cut hc
  let pars := metadata ha (tags G needs)
  have hMeta : MetadataCorrect (tags G needs) pars := metadata_correct ha _
  exact R.reflect_diagram_of_queries G needs hnv cut hc f hf β hb hn K θ hR.index_le hR
    pars (omegaIndex (tags G needs)) (family G needs hnv K cut θ f hAdm)
    (family_sound G needs hnv K cut θ f hAdm hR.index_le pars hMeta)
    (family_complete G needs hnv K cut θ f hAdm (hR.index_le.trans (hb cut hc).le) hβ
      (Auxiliary.inclusion (LStageZF_mono (hb cut hc).le) ∘ pars)
      (hMeta.inclusion (hb cut hc).le))

end OneYTruth.RootSemantics

#print axioms OneYTruth.RootSemantics.actual_finiteReflection
