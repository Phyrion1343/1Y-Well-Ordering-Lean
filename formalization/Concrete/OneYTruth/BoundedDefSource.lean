import OneYTruth.PureDefSource
import OneYTruth.PureSigmaBounded
import OneYTruth.PureSchemaRestriction

/-! Native bounded Def certificate with one common witness-bound parameter.
Its existence is supplied internally from the real schemas. -/

namespace OneYTruth.BoundedDefSource

open Constructible Constructible.Delta0Formula Constructible.Model
open InternalClosure PureSatisfactionMatrix

universe u v

noncomputable def certificate :
    PureSigmaBounded.Certificate.{u} (PureDefSource.query.{u+1,0} 0 Empty) :=
  PureSigmaBounded.certificate (PureDefSource.query_isSigmaOne 0 Empty) (by decide)

/-- U, omega, zero, D, common bound. -/
noncomputable def formula : Delta0Formula 5 := certificate.{u}.formula

theorem sound {V : ZFSet.{u}} (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (p : Fin 4 → ZFCarrier V) (B : ZFCarrier V)
    (hOmega : (p 1).val = Ordinal.omega0.toZFSet) (hZero : (p 2).val = ∅)
    (h : Satisfies ZFMem formula.{u} (snoc (fun i => (p i).val) B.val)) :
    (p 3).val = DefZF (p 0).val := by
  have hq := certificate.sound hV (interpretation V) rfl p B h
  exact PureDefSource.query_sound hV (interpretation V) rfl
    ⟨(p 0).val,hVL _ (p 0).property⟩ p rfl hOmega hZero hq

theorem monotone (p : Fin 4 → ZFSet.{u}) {B C : ZFSet.{u}} (hBC : B ⊆ C)
    (h : Satisfies ZFMem formula.{u} (snoc p B)) :
    Satisfies ZFMem formula.{u} (snoc p C) := certificate.monotone p hBC h

theorem complete {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    (p : Fin 4 → ZFCarrier V)
    (hOmega : (p 1).val = Ordinal.omega0.toZFSet) (hZero : (p 2).val = ∅)
    (hD : (p 3).val = DefZF (p 0).val) :
    ∃ B : ZFCarrier V, Satisfies ZFMem formula.{u} (snoc (fun i => (p i).val) B.val) := by
  have hMmem : N.mem = (interpretation V).mem := hmem
  have hCp := PureSchemaRestriction.collection N (interpretation V) hMmem hCol
  have hSp := PureSchemaRestriction.separation N (interpretation V) hMmem hSep
  have hq := (PureDefSource.realize_query_iff hV (interpretation V) rfl hCp hSp hpair hUnion
    ⟨(p 0).val,hVL _ (p 0).property⟩ p rfl hOmega hZero).mpr hD
  exact certificate.complete hV hpair hUnion (hZero ▸ (p 2).property) (interpretation V) rfl p hq

end OneYTruth.BoundedDefSource

#print axioms OneYTruth.BoundedDefSource.sound
#print axioms OneYTruth.BoundedDefSource.complete
