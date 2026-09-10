import OneYTruth.PureDefTranslation
import OneYTruth.DirectSchemaCorrect

/-! The two-sided complete-family test for Def(U), on actual pure sources.
The empty domain will have a separate base clause in the bounded formula. -/

namespace OneYTruth.PureDefCertificate

open Constructible FirstOrder FirstOrder.Language FormulaCode InternalNodes DirectSchema

universe u

def Matches (U A S e p b : ZFSet.{u}) : Prop :=
  b ⊆ U ∧ ∀ x ∈ U, x ∈ b ↔ ExtendedHolds A S e p x

def Check (U F A nodes S D : ZFSet.{u}) : Prop :=
  (∀ e ∈ F, ∀ p ∈ A, ScopeOne U A nodes e p → ∃ b ∈ D, Matches U A S e p b) ∧
    (∀ b ∈ D, ∃ e ∈ F, ∃ p ∈ A, ScopeOne U A nodes e p ∧ Matches U A S e p b)

theorem matches_codes {U b : ZFSet.{u}} (N : Interpretation 0 Empty (ZFCarrier U))
    {n : Nat} (φ : (language 0 Empty).BoundedFormula Empty (n+1)) (xs : Fin n → ZFCarrier U) :
    Matches U (assignmentCodes U) (satisfactionSet Empty.elim N)
      (packedCode Empty.elim ⟨n+1, φ⟩) (assignmentCode xs) b ↔
      b ⊆ U ∧ ∀ x : ZFCarrier U, x.val ∈ b ↔ realize N φ Empty.elim (Fin.snoc xs x) := by
  have hi : Function.Injective (Empty.elim : Empty → ZFSet.{u}) := fun e => e.elim
  apply and_congr_right
  intro _
  constructor
  · intro h x
    exact (h x.val x.property).trans (extendedHolds_satisfaction Empty.elim hi N φ xs x)
  · intro h x hx
    exact (h ⟨x, hx⟩).trans (extendedHolds_satisfaction Empty.elim hi N φ xs ⟨x, hx⟩).symm

theorem matches_unique {U A S e p b c : ZFSet.{u}}
    (hb : Matches U A S e p b) (hc : Matches U A S e p c) : b = c := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    exact (hc.2 x (hb.1 hx)).mpr ((hb.2 x (hb.1 hx)).mp hx)
  · intro hx
    exact (hb.2 x (hc.1 hx)).mpr ((hc.2 x (hc.1 hx)).mp hx)

theorem check_iff_eq_DefZF {U D : ZFSet.{u}} [Nonempty (ZFCarrier U)]
    (N : Interpretation 0 Empty (ZFCarrier U)) (hmem : N.mem = zfCarrierMem U) :
    Check U (syntaxCodes (k := 0) (Empty.elim : Empty → ZFSet.{u})) (assignmentCodes U)
      (scopedPairs (k := 0) U Empty.elim) (satisfactionSet Empty.elim N) D ↔ D = DefZF U := by
  constructor
  · intro h
    apply ZFSet.ext
    intro b
    constructor
    · intro hb
      obtain ⟨e, he, p, hp, hs, hm⟩ := h.2 b hb
      obtain ⟨⟨m, φ⟩, rfl⟩ := ZFSet.mem_range.mp he
      obtain ⟨⟨n, xs⟩, rfl⟩ := ZFSet.mem_range.mp hp
      have hmn : m = n+1 := (scopeOne_codes Empty.elim φ xs).mp hs
      subst m
      obtain ⟨hbU, hφ⟩ := (matches_codes N φ xs).mp hm
      exact (PureDefTranslation.mem_DefZF_iff_mixed N hmem).mpr ⟨hbU, n, xs, φ, hφ⟩
    · intro hb
      obtain ⟨hbU, n, xs, φ, hφ⟩ := (PureDefTranslation.mem_DefZF_iff_mixed N hmem).mp hb
      have he : packedCode (Empty.elim : Empty → ZFSet.{u}) ⟨n+1, φ⟩ ∈
          syntaxCodes (k := 0) (Empty.elim : Empty → ZFSet.{u}) :=
        ZFSet.mem_range_self (f := packedCode (k := 0) (Empty.elim : Empty → ZFSet.{u})) ⟨n+1, φ⟩
      have hp : assignmentCode xs ∈ assignmentCodes U :=
        ZFSet.mem_range_self (f := fun w : PackedAssignment U => assignmentCode w.2) ⟨n, xs⟩
      obtain ⟨c, hc, hm⟩ := h.1 _ he _ hp ((scopeOne_codes Empty.elim φ xs).mpr rfl)
      have hbc := matches_unique ((matches_codes N φ xs).mpr ⟨hbU, hφ⟩) hm
      exact hbc.symm ▸ hc
  · rintro rfl
    constructor
    · intro e he p hp hs
      obtain ⟨⟨m, φ⟩, rfl⟩ := ZFSet.mem_range.mp he
      obtain ⟨⟨n, xs⟩, rfl⟩ := ZFSet.mem_range.mp hp
      have hmn : m = n+1 := (scopeOne_codes Empty.elim φ xs).mp hs
      subst m
      let b := ZFSet.sep (fun x => ∃ hx : x ∈ U, realize N φ Empty.elim (Fin.snoc xs ⟨x, hx⟩)) U
      have hbU : b ⊆ U := fun _ hx => (ZFSet.mem_sep.mp hx).1
      have hφ (x : ZFCarrier U) : x.val ∈ b ↔ realize N φ Empty.elim (Fin.snoc xs x) := by
        rw [show b = ZFSet.sep (fun y => ∃ hy : y ∈ U, realize N φ Empty.elim (Fin.snoc xs ⟨y, hy⟩)) U from rfl,
          ZFSet.mem_sep]
        change (x.val ∈ U ∧ ∃ hx : x.val ∈ U, realize N φ Empty.elim (Fin.snoc xs ⟨x.val, hx⟩)) ↔ _
        exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨x.property, x.property, h⟩⟩
      exact ⟨b, (PureDefTranslation.mem_DefZF_iff_mixed N hmem).mpr ⟨hbU, n, xs, φ, hφ⟩,
        (matches_codes N φ xs).mpr ⟨hbU, hφ⟩⟩
    · intro b hb
      obtain ⟨hbU, n, xs, φ, hφ⟩ := (PureDefTranslation.mem_DefZF_iff_mixed N hmem).mp hb
      exact ⟨packedCode Empty.elim ⟨n+1, φ⟩,
        ZFSet.mem_range_self (f := packedCode (k := 0) (Empty.elim : Empty → ZFSet.{u})) ⟨n+1, φ⟩,
        assignmentCode xs,
        ZFSet.mem_range_self (f := fun w : PackedAssignment U => assignmentCode w.2) ⟨n, xs⟩,
        (scopeOne_codes Empty.elim φ xs).mpr rfl, (matches_codes N φ xs).mpr ⟨hbU, hφ⟩⟩

end OneYTruth.PureDefCertificate
