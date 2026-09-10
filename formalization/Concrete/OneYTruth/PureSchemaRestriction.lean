import OneYTruth.PureDefTranslation

/-! Mixed Separation and Collection supply the real schemas in the pure
membership reduct on the same carrier. No absoluteness is used. -/

namespace OneYTruth.PureSchemaRestriction

open Constructible FirstOrder FirstOrder.Language InternalClosure

universe u v

theorem realize_translation {K : Nat} {J : Type v} {A : Type u}
    (N : Interpretation K J A) (M : Interpretation 0 Empty A) (hmem : N.mem = M.mem)
    {n : Nat} (φ : (language 0 Empty).BoundedFormula Empty n) (p : Fin n → A) :
    realize N (ofConstructibleFO K J (PureDefTranslation.toFO φ)) Empty.elim p ↔
      realize M φ Empty.elim p := by
  rw [realize_ofConstructibleFO,hmem]
  exact PureDefTranslation.satisfies_toFO M φ p

theorem separation {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (N : Interpretation K J (ZFCarrier V)) (M : Interpretation 0 Empty (ZFCarrier V))
    (hmem : N.mem = M.mem) (h : HasSeparation N) : HasSeparation M := by
  intro n φ p a
  obtain ⟨b,hb⟩ := h n (ofConstructibleFO K J (PureDefTranslation.toFO φ)) p a
  exact ⟨b,fun x => (hb x).trans (and_congr Iff.rfl (realize_translation N M hmem φ _))⟩

theorem collection {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (N : Interpretation K J (ZFCarrier V)) (M : Interpretation 0 Empty (ZFCarrier V))
    (hmem : N.mem = M.mem) (h : HasCollection N) : HasCollection M := by
  intro n φ p a ht
  have htotal : ∀ x : ZFCarrier V, x.val ∈ a.val → ∃ y : ZFCarrier V,
      realize N (ofConstructibleFO K J (PureDefTranslation.toFO φ)) Empty.elim
        (Fin.snoc (Fin.snoc p x) y) := by
    intro x hx
    obtain ⟨y,hy⟩ := ht x hx
    exact ⟨y,(realize_translation N M hmem φ _).mpr hy⟩
  obtain ⟨b,hb⟩ := h n (ofConstructibleFO K J (PureDefTranslation.toFO φ)) p a htotal
  refine ⟨b,?_⟩
  intro x hx
  obtain ⟨y,hy,hyφ⟩ := hb x hx
  exact ⟨y,hy,(realize_translation N M hmem φ _).mp hyφ⟩

end OneYTruth.PureSchemaRestriction

#print axioms OneYTruth.PureSchemaRestriction.collection
