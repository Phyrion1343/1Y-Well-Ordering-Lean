import OneYTruth.CollectionReplacement

/-!
# Finite Cartesian products without Power Set

Two actual pure bounded Replacement instances and closure under ordered
pairs and union suffice. Pair slices are internalized first, then their
family, then its union. Each resulting set is identified with its actual
external range; no external image is silently treated as internal.
-/

namespace OneYTruth.InternalProducts

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula InternalClosure

universe u v

theorem range_carrier_val_eq (A : ZFSet.{u}) :
    ZFSet.range (Subtype.val : ZFCarrier A → ZFSet.{u}) = A := by
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_range]
  exact ⟨fun ⟨a, h⟩ => h ▸ a.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

noncomputable def pairSlice (B : ZFSet.{u}) (a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun b : ZFCarrier B => ZFSet.pair a b.val)

noncomputable def pairProduct (A B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun z : ZFCarrier A × ZFCarrier B => ZFSet.pair z.1.val z.2.val)

def pairFormula (k : Nat) (I : Type v) : (language k I).BoundedFormula Empty 3 :=
  ofConstructibleDeltaZero k I (kuratowskiPairEqAt 2 0 1)

theorem realize_pairFormula {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V) (a b p : ZFCarrier V) :
    OneYTruth.realize N (pairFormula k I) Empty.elim (Fin.snoc (Fin.snoc ![a] b) p) ↔
      p.val = ZFSet.pair a.val b.val := by
  rw [pairFormula, realize_ofConstructibleDeltaZero_absolute hV N hmem,
    satisfies_kuratowskiPairEqAt]
  rfl

/-- One Replacement instance makes the entire slice `{(a,b) | b∈B}` internal. -/
theorem pairSlice_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (hRep : ReplacementInstance N (pairFormula k I))
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    {B a : ZFSet.{u}} (hB : B ∈ V) (ha : a ∈ V) : pairSlice B a ∈ V := by
  have hsource : ZFSet.range (Subtype.val : ZFCarrier B → ZFSet.{u}) ∈ V := by
    rw [range_carrier_val_eq]
    exact hB
  apply image_range_mem hV N (pairFormula k I) hRep ![⟨a, ha⟩]
    Subtype.val (fun b : ZFCarrier B => ZFSet.pair a b.val) Subtype.val_injective hsource
    (fun b => hpair a ha b.val (hV.mem_trans b.property hB))
  intro x y hx
  rw [range_carrier_val_eq] at hx
  rw [realize_pairFormula hV N hmem]
  constructor
  · intro h
    exact ⟨⟨x.val, hx⟩, rfl, h.symm⟩
  · rintro ⟨b, hb, hby⟩
    simpa only [hb] using hby.symm

/-- Coordinates are B, a, T; this formula asserts that T is exactly the pair slice. -/
def sliceGraphFormula : Delta0Formula 3 :=
  .conj
    (.boundedAll 2 (.boundedEx 0 (kuratowskiPairEqAt 3 1 4)))
    (.boundedAll 0 (.boundedEx 2 (kuratowskiPairEqAt 4 1 3)))

theorem satisfies_sliceGraphFormula (B a T : ZFSet.{u}) :
    Satisfies ZFMem sliceGraphFormula ![B, a, T] ↔ T = pairSlice B a := by
  simp only [sliceGraphFormula, Satisfies, satisfies_boundedAll, satisfies_kuratowskiPairEqAt]
  change ((∀ p ∈ T, ∃ b ∈ B, p = ZFSet.pair a b) ∧
      ∀ b ∈ B, ∃ p ∈ T, p = ZFSet.pair a b) ↔ T = pairSlice B a
  constructor
  · rintro ⟨hleft, hright⟩
    apply ZFSet.ext
    intro p
    constructor
    · intro hp
      obtain ⟨b, hb, heq⟩ := hleft p hp
      exact ZFSet.mem_range.mpr ⟨⟨b, hb⟩, heq.symm⟩
    · intro hp
      obtain ⟨b, heq⟩ := ZFSet.mem_range.mp hp
      obtain ⟨q, hq, hqb⟩ := hright b.val b.property
      exact (hqb.trans heq) ▸ hq
  · intro h
    subst T
    constructor
    · intro p hp
      obtain ⟨b, heq⟩ := ZFSet.mem_range.mp hp
      exact ⟨b.val, b.property, heq.symm⟩
    · intro b hb
      exact ⟨ZFSet.pair a b, ZFSet.mem_range_self (f := fun z : ZFCarrier B =>
        ZFSet.pair a z.val) ⟨b, hb⟩, rfl⟩

def mixedSliceGraphFormula (k : Nat) (I : Type v) :=
  ofConstructibleDeltaZero k I sliceGraphFormula

theorem realize_mixedSliceGraphFormula {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V) (B a T : ZFCarrier V) :
    OneYTruth.realize N (mixedSliceGraphFormula k I) Empty.elim
      (Fin.snoc (Fin.snoc ![B] a) T) ↔ T.val = pairSlice B.val a.val := by
  rw [mixedSliceGraphFormula, realize_ofConstructibleDeltaZero_absolute hV N hmem]
  have heq : Constructible.Delta0Formula.val (Fin.snoc (Fin.snoc ![B] a) T) =
      ![B.val, a.val, T.val] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact satisfies_sliceGraphFormula B.val a.val T.val

/-- A second Replacement instance internalizes the family of all slices. -/
theorem sliceFamily_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (hRepPair : ReplacementInstance N (pairFormula k I))
    (hRepSlice : ReplacementInstance N (mixedSliceGraphFormula k I))
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    {A B : ZFSet.{u}} (hA : A ∈ V) (hB : B ∈ V) :
    ZFSet.range (fun a : ZFCarrier A => pairSlice B a.val) ∈ V := by
  have hsource : ZFSet.range (Subtype.val : ZFCarrier A → ZFSet.{u}) ∈ V := by
    rw [range_carrier_val_eq]
    exact hA
  apply image_range_mem hV N (mixedSliceGraphFormula k I) hRepSlice ![⟨B, hB⟩]
    Subtype.val (fun a : ZFCarrier A => pairSlice B a.val) Subtype.val_injective hsource
    (fun a => pairSlice_mem hV N hmem hRepPair hpair hB (hV.mem_trans a.property hA))
  intro x y hx
  rw [range_carrier_val_eq] at hx
  rw [realize_mixedSliceGraphFormula hV N hmem]
  exact ⟨fun h => ⟨⟨x.val, hx⟩, rfl, h.symm⟩,
    fun ⟨a, ha, hay⟩ => by simpa only [ha] using hay.symm⟩

theorem sUnion_sliceFamily (A B : ZFSet.{u}) :
    ZFSet.sUnion (ZFSet.range (fun a : ZFCarrier A => pairSlice B a.val)) = pairProduct A B := by
  apply ZFSet.ext
  intro p
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨T, hT, hp⟩
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hT
    obtain ⟨b, hb⟩ := ZFSet.mem_range.mp hp
    exact ZFSet.mem_range.mpr ⟨(a, b), hb⟩
  · intro hp
    obtain ⟨⟨a, b⟩, h⟩ := ZFSet.mem_range.mp hp
    exact ⟨pairSlice B a.val, ZFSet.mem_range_self a, ZFSet.mem_range.mpr ⟨b, h⟩⟩

/-- Exact internal product existence from the two Replacement instances and elementary closure. -/
theorem pairProduct_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (hRepPair : ReplacementInstance N (pairFormula k I))
    (hRepSlice : ReplacementInstance N (mixedSliceGraphFormula k I))
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    {A B : ZFSet.{u}} (hA : A ∈ V) (hB : B ∈ V) : pairProduct A B ∈ V := by
  rw [← sUnion_sliceFamily]
  exact hUnion _ (sliceFamily_mem hV N hmem hRepPair hRepSlice hpair hA hB)

end OneYTruth.InternalProducts
