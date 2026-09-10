import OneYTruth.AuxiliarySkolem

/-!
# Elementarity of the local reducts of an auxiliary elementary substructure

The named symbols remain separate. Their indices and the finitely many
block numbers are parameters of the auxiliary translation. This module
transfers actual formula truth through that translation; it does not
identify a restricted ambient truth tower with a smaller domain's tower.
-/

namespace OneYTruth.Auxiliary

open FirstOrder FirstOrder.Language

universe u v w

variable {A : Type u} (M : Interpretation A)

def onSet (s : Set A) : Interpretation s where
  mem a b := M.mem a.val b.val
  truth b ξ e a := M.truth b.val ξ.val e.val a.val

theorem onSet_structure (S : @language.Substructure A M.structure) :
    (onSet M (S : Set A)).structure =
      @Substructure.inducedStructure language A M.structure S := by
  apply FirstOrder.Language.Structure.ext
  · funext n e
    nomatch e
  · funext n r xs
    cases r <;> rfl

/-- Every actual auxiliary formula is absolute across an elementary substructure. -/
theorem realize_onSet (S : @language.ElementarySubstructure A M.structure)
    {α : Type v} {n : Nat} (φ : language.BoundedFormula α n)
    (v : α → S) (xs : Fin n → S) :
    realize (onSet M (S : Set A)) φ v xs ↔
      realize M φ (fun i => (v i).val) (fun i => (xs i).val) := by
  letI := M.structure
  have hstr : (onSet M (S : Set A)).structure =
      @Substructure.inducedStructure language A M.structure S.toSubstructure :=
    onSet_structure M S.toSubstructure
  unfold realize
  rw [hstr]
  exact (S.subtype.map_boundedFormula φ v xs).symm

/-- Full formula preservation for all separately named local predicates whose
index parameters lie in the substructure. -/
theorem realize_reduct_onSet (S : @language.ElementarySubstructure A M.structure)
    {k : Nat} {I : Type v} {α : Type w} {n : Nat}
    (block : Fin (k + 1) → S) (index : I → S)
    (φ : (OneYTruth.language k I).BoundedFormula α n)
    (v : α → S) (xs : Fin n → S) :
    OneYTruth.realize (reduct (onSet M (S : Set A)) block index) φ v xs ↔
      OneYTruth.realize (reduct M (fun j => (block j).val) (fun i => (index i).val))
        φ (fun i => (v i).val) (fun i => (xs i).val) := by
  rw [← realize_translate (onSet M (S : Set A)) block index,
    realize_onSet M S]
  have hv : (fun i => (Sum.elim v (Sum.elim block index) i).val) =
      Sum.elim (fun i => (v i).val)
        (Sum.elim (fun j => (block j).val) (fun i => (index i).val)) := by
    funext i
    rcases i with i | j
    · rfl
    · rcases j with j | j <;> rfl
  rw [hv, realize_translate]

end OneYTruth.Auxiliary
