import OneYTruth.AuxiliaryPureTranslation
import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistoryBounds

/-!
# Auxiliary formulas interpreted inside an actual set domain

The syntax is exactly `AuxiliaryCode.translate`.  Its semantic correctness
requires only that the ambient set be transitive and closed under ordered
pairing.  In particular, no Separation or Collection scheme over the proper
class `L` is used in this transfer theorem.
-/

namespace OneYTruth.AuxiliaryCode

open Constructible Constructible.Model Constructible.ContinuumFormula
open FirstOrder FirstOrder.Language

universe u

theorem isKuratowskiPairOf_set_iff {D : ZFSet.{u}} (hD : D.IsTransitive)
    (p x y : ZFCarrier D) :
    IsKuratowskiPairOf (zfCarrierMem D) p x y ↔
      p.val = ZFSet.pair x.val y.val := by
  have hsemantic := satisfies_kuratowskiPairAt (zfCarrierMem D)
    (0 : Fin 3) 1 2 ![p, x, y]
  rw [show kuratowskiPairAt (0 : Fin 3) 1 2 =
      (Delta0Formula.kuratowskiPairEqAt (0 : Fin 3) 1 2).toFO from rfl,
    Delta0Formula.satisfies_toFO_absolute hD,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt] at hsemantic
  exact hsemantic.symm

theorem satisfies_graphRelFormula_set {D : ZFSet.{u}} (hD : D.IsTransitive)
    (s : Tuple (ZFCarrier D) 3) :
    FOFormula.Satisfies (zfCarrierMem D) graphRelFormula s ↔
      ZFSet.pair (s 1).val (s 2).val ∈ (s 0).val := by
  rw [graphRelFormula, Delta0Formula.satisfies_toFO_absolute hD]
  simp only [Delta0Formula.satisfies_toFO, graphRelDelta0,
    Delta0Formula.Satisfies, Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro h
    exact ⟨ZFSet.pair (s 1).val (s 2).val, h, rfl⟩

theorem satisfies_relationFormula_set {D : ZFSet.{u}} (hD : D.IsTransitive)
    (hpair : ∀ {x y : ZFSet.{u}}, x ∈ D → y ∈ D → ZFSet.pair x y ∈ D)
    (s : Tuple (ZFCarrier D) 5) :
    FOFormula.Satisfies (zfCarrierMem D) relationFormula s ↔
      ZFSet.pair (ZFSet.pair (s 1).val (s 2).val)
        (ZFSet.pair (s 3).val (s 4).val) ∈ (s 0).val := by
  change (∃ p q : ZFCarrier D,
    FOFormula.Satisfies (zfCarrierMem D) (kuratowskiPairAt 5 1 2)
      (snoc (snoc s p) q) ∧
    FOFormula.Satisfies (zfCarrierMem D) (kuratowskiPairAt 6 3 4)
      (snoc (snoc s p) q) ∧
    FOFormula.Satisfies (zfCarrierMem D)
      (FOFormula.rename ![0, 5, 6] graphRelFormula) (snoc (snoc s p) q)) ↔ _
  simp only [satisfies_kuratowskiPairAt, FOFormula.satisfies_rename,
    satisfies_graphRelFormula_set hD]
  change (∃ p q : ZFCarrier D,
    IsKuratowskiPairOf (zfCarrierMem D) p (s 1) (s 2) ∧
    IsKuratowskiPairOf (zfCarrierMem D) q (s 3) (s 4) ∧
    ZFSet.pair p.val q.val ∈ (s 0).val) ↔ _
  simp only [isKuratowskiPairOf_set_iff hD]
  constructor
  · rintro ⟨p, q, hp, hq, hW⟩
    simpa only [hp, hq] using hW
  · intro hW
    exact ⟨⟨ZFSet.pair (s 1).val (s 2).val, hpair (s 1).property (s 2).property⟩,
      ⟨ZFSet.pair (s 3).val (s 4).val, hpair (s 3).property (s 4).property⟩,
      rfl, rfl, hW⟩

section SetDomain

variable {D : ZFSet.{u}}

local instance : Language.setTheory.Structure (ZFCarrier D) :=
  setTheoryStructure (zfCarrierMem D)

theorem realize_truthAtom_set (hD : D.IsTransitive)
    (hpair : ∀ {x y : ZFSet.{u}}, x ∈ D → y ∈ D → ZFSet.pair x y ∈ D)
    {n : Nat} (is : Fin 4 → Fin n)
    (params : Fin 2 → ZFCarrier D) (xs : Fin n → ZFCarrier D) :
    (truthAtom is).Realize params xs ↔
      ZFSet.pair (ZFSet.pair (xs (is 0)).val (xs (is 1)).val)
        (ZFSet.pair (xs (is 2)).val (xs (is 3)).val) ∈ (params 1).val := by
  rw [truthAtom, BoundedFormula.realize_relabel]
  have hv : Sum.elim params (xs ∘ Fin.castAdd 0) ∘ Sum.elim Empty.elim (atomMap is) =
      Sum.elim Empty.elim (fun j => Sum.elim params xs (atomMap is j)) := by
    funext i
    cases i with
    | inl e => nomatch e
    | inr j => rfl
  rw [hv, Formula.boundedFormula_realize_eq_realize, BoundedFormula.realize_toFormula]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  change translatedRealizes (zfCarrierMem D) relationFormula _ ↔ _
  rw [realize_toBoundedFormula, satisfies_relationFormula_set hD hpair]
  rfl

/-- The inclusion of an element of an internal domain into the ambient set. -/
def intoSet (hD : D.IsTransitive) (U : ZFCarrier D)
    (x : ZFCarrier U.val) : ZFCarrier D :=
  ⟨x.val, hD.mem_trans x.property U.property⟩

theorem intoSet_snoc (hD : D.IsTransitive) (U : ZFCarrier D) {n : Nat}
    (xs : Fin n → ZFCarrier U.val) (x : ZFCarrier U.val) :
    (fun i => intoSet hD U ((Fin.snoc xs x : Fin (n + 1) → ZFCarrier U.val) i)) =
      Fin.snoc (fun i => intoSet hD U (xs i)) (intoSet hD U x) :=
  Fin.comp_snoc (intoSet hD U) xs x

/-- Relativization to `U` is correct inside any transitive pair-closed set `D`. -/
theorem realize_translate_set (hD : D.IsTransitive)
    (hpair : ∀ {x y : ZFSet.{u}}, x ∈ D → y ∈ D → ZFSet.pair x y ∈ D)
    (U W : ZFCarrier D) {n : Nat}
    (φ : Auxiliary.language.BoundedFormula Empty n) (xs : Fin n → ZFCarrier U.val) :
    (translate φ).Realize ![U, W] (fun i => intoSet hD U (xs i)) ↔
      Auxiliary.realize (interpretation U.val W.val) φ Empty.elim xs := by
  classical
  induction φ with
  | falsum => rfl
  | equal t s =>
      change intoSet hD U (xs (termIndex t)) = intoSet hD U (xs (termIndex s)) ↔
        @Term.realize _ _ (interpretation U.val W.val).structure _ (Sum.elim Empty.elim xs) t =
          @Term.realize _ _ (interpretation U.val W.val).structure _ (Sum.elim Empty.elim xs) s
      rw [realize_termIndex, realize_termIndex]
      exact ⟨fun h => Subtype.ext (congrArg (fun z : ZFCarrier D => z.val) h),
        congrArg (intoSet hD U)⟩
  | rel r ts =>
      cases r with
      | mem =>
          change (xs (termIndex (ts 0))).val ∈ (xs (termIndex (ts 1))).val ↔ _
          simp only [Auxiliary.realize, BoundedFormula.Realize, realize_termIndex]
          rfl
      | truth =>
          rw [translate, realize_truthAtom_set hD hpair]
          simp only [Auxiliary.realize, BoundedFormula.Realize,
            realize_termIndex, intoSet, Matrix.cons_val_one, Matrix.cons_val_zero]
          rfl
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ xs) (ihψ xs)
  | @all n φ ih =>
      simp only [translate, Auxiliary.realize, BoundedFormula.Realize,
        setTheoryStructure_relMap, Matrix.cons_val_zero, Matrix.cons_val_one,
        Term.realize, Sum.elim_inr, Sum.elim_inl, Fin.snoc_last, zfCarrierMem]
      change (∀ z : ZFCarrier D, z.val ∈ U.val →
        (translate φ).Realize ![U, W] (Fin.snoc (fun i => intoSet hD U (xs i)) z)) ↔
          ∀ x : ZFCarrier U.val, Auxiliary.realize (interpretation U.val W.val)
            φ Empty.elim (Fin.snoc xs x)
      constructor
      · intro h x
        apply (ih (Fin.snoc xs x)).mp
        rw [intoSet_snoc]
        exact h (intoSet hD U x) x.property
      · intro h z hz
        let x : ZFCarrier U.val := ⟨z.val, hz⟩
        have hφ := (ih (Fin.snoc xs x)).mpr (h x)
        rw [intoSet_snoc] at hφ
        have hx : intoSet hD U x = z := Subtype.ext rfl
        simpa only [hx] using hφ

end SetDomain

/-- A nonzero limit constructible stage supplies all pair witnesses. -/
theorem realize_translate_stage {δ : Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    (U W : ZFCarrier (LStageZF δ)) {n : Nat}
    (φ : Auxiliary.language.BoundedFormula Empty n) (xs : Fin n → ZFCarrier U.val) :
    letI : Language.setTheory.Structure (ZFCarrier (LStageZF δ)) :=
      setTheoryStructure (zfCarrierMem (LStageZF δ))
    (translate φ).Realize ![U, W]
      (fun i => intoSet (LStageZF_isTransitive δ) U (xs i)) ↔
      Auxiliary.realize (interpretation U.val W.val) φ Empty.elim xs :=
  realize_translate_set (LStageZF_isTransitive δ)
    (orderedPair_mem_LStageZF_of_isSuccLimit hδ) U W φ xs

#print axioms realize_translate_set
#print axioms realize_translate_stage

end OneYTruth.AuxiliaryCode
