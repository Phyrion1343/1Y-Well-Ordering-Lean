import OneYTruth.ConstructibleBoundedIteration

/-! A fixed pure formula for the whole union of an actual uniform omega family. -/

namespace OneYTruth.UniformUnionFormula

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open Constructible.IndexedSequenceZF

universe u

def memberMatrix {p : Nat} (φ : FOFormula (p + 2)) : FOFormula (p + 4) :=
  .conj (.mem (Fin.last (p + 1)).castSucc.castSucc (Fin.last p).castSucc.castSucc.castSucc)
    (.conj (finiteIterationStepFormulaAt φ
      (fun i => i.castSucc.castSucc.castSucc.castSucc)
      (Fin.last (p + 1)).castSucc.castSucc (Fin.last (p + 3)))
      (.mem (Fin.last (p + 2)).castSucc (Fin.last (p + 3))))

/- The external layout is params,omega,node; the two witnesses are index,value. -/
def member {p : Nat} (φ : FOFormula (p + 2)) : FOFormula (p + 2) :=
  .ex (.ex (.conj (.mem (Fin.last (p + 2)).castSucc (Fin.last p).castSucc.castSucc.castSucc)
    (.conj (finiteIterationStepFormulaAt φ
      (fun i => i.castSucc.castSucc.castSucc.castSucc)
      (Fin.last (p + 2)).castSucc (Fin.last (p + 3)))
      (.mem (Fin.last (p + 1)).castSucc.castSucc (Fin.last (p + 3))))))

theorem satisfies_member {p : Nat} (φ : FOFormula (p + 2))
    (params : Tuple LCarrier.{u} p) (W z : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem (member φ) (snoc (snoc params W) z) ↔
      ∃ n S : LCarrier.{u}, n.val ∈ W.val ∧
        FOFormula.Satisfies lCarrierMem φ (snoc (snoc params n) S) ∧ z.val ∈ S.val := by
  simp only [member, FOFormula.Satisfies, satisfies_finiteIterationStepFormulaAt,
    snoc_last, snoc_castSucc, lCarrierMem]

theorem satisfies_member_family {p : Nat} (spec : ParametricUniformOmegaFamilySpec.{u} p)
    (z : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem (member spec.formula) (snoc (snoc spec.params omegaLCarrier) z) ↔
      z.val ∈ (parametricUniformOmegaUnion spec).val := by
  rw [satisfies_member, mem_parametricUniformOmegaUnion_iff]
  constructor
  · rintro ⟨n,S,hn,hS,hz⟩
    obtain ⟨m,hm⟩ := (mem_omega_iff_exists_natCode n.val).mp hn
    have hn' : n = natLCarrier m := Subtype.ext hm
    subst n
    have hS' := (spec.realizes m S).mp hS
    exact ⟨m,hS' ▸ hz⟩
  · rintro ⟨m,hm⟩
    exact ⟨natLCarrier m,spec.value m,
      (mem_omega_iff_exists_natCode _).mpr ⟨m,rfl⟩,
      (spec.realizes m _).mpr rfl,hm⟩

/-- Parameters followed by omega and the proposed whole union. -/
def graph {p : Nat} (φ : FOFormula (p + 2)) : FOFormula (p + 2) :=
  .all (.biimp (.mem (Fin.last (p + 2)) (Fin.last (p + 1)).castSucc)
    (FOFormula.rename
      (Fin.lastCases (Fin.last (p + 2)) (fun i => i.castSucc.castSucc)) (member φ)))

theorem satisfies_graph {p : Nat} (φ : FOFormula (p + 2))
    (params : Tuple LCarrier.{u} p) (W S : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem (graph φ) (snoc (snoc params W) S) ↔
      ∀ z : LCarrier.{u}, z.val ∈ S.val ↔
        FOFormula.Satisfies lCarrierMem (member φ) (snoc (snoc params W) z) := by
  simp only [graph, FOFormula.satisfies_all, FOFormula.satisfies_biimp,
    FOFormula.Satisfies, FOFormula.satisfies_rename, snoc_last, snoc_castSucc, lCarrierMem]
  apply forall_congr'
  intro z
  have hv : (fun i => snoc (snoc (snoc params W) S) z
      (Fin.lastCases (Fin.last (p + 2)) (fun i => i.castSucc.castSucc) i)) =
      snoc (snoc params W) z := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  rw [hv]

theorem satisfies_graph_family {p : Nat} (spec : ParametricUniformOmegaFamilySpec.{u} p)
    (S : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem (graph spec.formula) (snoc (snoc spec.params omegaLCarrier) S) ↔
      S = parametricUniformOmegaUnion spec := by
  rw [satisfies_graph]
  simp only [satisfies_member_family]
  constructor
  · intro h
    apply Subtype.ext
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact (h ⟨z,mem_L_of_mem hz S.property⟩).mp hz
    · intro hz
      exact (h ⟨z,mem_L_of_mem hz (parametricUniformOmegaUnion spec).property⟩).mpr hz
  · rintro rfl
    exact fun _ => Iff.rfl

end OneYTruth.UniformUnionFormula
