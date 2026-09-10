import OneYTruth.InternalPureSatisfaction
import OneYTruth.PureDefFormula

/-! A normative Sigma-one definition of Def(U), using only U, omega, zero,
and the proposed output. Every satisfaction and syntax source is checked. -/

namespace OneYTruth.PureDefSource

open Constructible Constructible.Model FirstOrder FirstOrder.Language
open PureSatisfactionMatrix InternalClosure InternalNodes

universe u v

/-- Four primitive inputs U, omega, zero, D; then Sat and eighteen sources. -/
def pureMap : Fin 22 → Fin 23 :=
  ![0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def defMap : Fin 7 → Fin 23 := ![0,11,12,15,4,3,2]

noncomputable def pureAt (K : Nat) (J : Type v) :=
  renameScope pureMap (PureSatisfactionSource.body.{u,v} K J)
def defAt (K : Nat) (J : Type v) :=
  renameScope defMap (PureDefCertificate.mixedFormula K J)

theorem pureAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (pureAt.{u,v} K J) :=
  (PureSatisfactionSource.body_isSigmaOne K J).renameScope _
theorem defAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (defAt K J) :=
  .deltaZero ((PureDefCertificate.mixedFormula_isDeltaZero K J).renameScope _)

noncomputable def body (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u} (pureAt.{u,v} K J) (defAt K J)
    (pureAt_isSigmaOne K J) (defAt_isSigmaOne K J)
theorem body_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (body.{u,v} K J) :=
  sigmaConjFormula_isSigmaOne _ _ _ _

theorem realize_body {K : Nat} {J : Type v} {A : Type u}
    (N : Interpretation K J A) (p : Fin 23 → A) :
    realize N (body.{u,v} K J) Empty.elim p ↔
      realize N (PureSatisfactionSource.body.{u,v} K J) Empty.elim (p ∘ pureMap) ∧
      realize N (PureDefCertificate.mixedFormula K J) Empty.elim (p ∘ defMap) := by
  rw [body,realize_sigmaConjFormula,pureAt,defAt,realize_renameScope,realize_renameScope]

theorem body_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (U : LCarrier.{u}) (p : Fin 23 → ZFCarrier V)
    (hU : (p 0).val = U.val) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅) (h : realize N (body.{u+1,v} K J) Empty.elim p) :
    (p 3).val = DefZF (p 0).val := by
  obtain ⟨hs,hd⟩ := (realize_body N p).mp h
  have hc := PureSatisfactionSource.body_sound hV N hmem U (p ∘ pureMap) hU hOmega hZero hs
  change (p 11).val = _ ∧ (p 12).val = _ ∧ (p 15).val = _ ∧ (p 4).val = _ at hc
  obtain ⟨hF,hA,hNodes,hSat⟩ := hc
  apply (PureDefCertificate.realize_formula_iff_DefZF
    (interpretation (p 0).val) rfl hV N hmem (p ∘ defMap) ?_).mp hd
  intro i
  fin_cases i <;> first | exact hF | exact hA | exact hNodes | exact hSat | exact hZero | rfl

noncomputable def query (K : Nat) (J : Type v) : (language K J).BoundedFormula Empty 4 :=
  existsSuffix 19 (body.{u,v} K J)

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u,v} K J) :=
  existsSuffix_isSigmaOne _ (body_isSigmaOne K J)

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (U : LCarrier.{u}) (p : Fin 4 → ZFCarrier V)
    (hU : (p 0).val = U.val) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅) (h : realize N (query.{u+1,v} K J) Empty.elim p) :
    (p 3).val = DefZF (p 0).val := by
  obtain ⟨w,hw⟩ := (realize_existsSuffix (m := 19) N (body.{u+1,v} K J) p).mp h
  exact body_sound hV N hmem U (Fin.append p w) hU hOmega hZero hw

theorem realize_query_iff {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    (U : LCarrier.{u}) (p : Fin 4 → ZFCarrier V)
    (hU : (p 0).val = U.val) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅) :
    realize N (query.{u+1,v} K J) Empty.elim p ↔ (p 3).val = DefZF U.val := by
  constructor
  · intro h
    simpa only [hU] using query_sound hV N hmem U p hU hOmega hZero h
  · intro hD
    have hw := PureSatisfactionSource.actual_mem hV N hmem hCol hSep hpair hUnion
      (hOmega ▸ (p 1).property) U (hU ▸ (p 0).property)
    let w : Fin 19 → ZFCarrier V := fun i => ⟨actual U.val (Fin.natAdd 3 i),hw _⟩
    let q := Fin.append p w
    have hq : ∀ i, (q (pureMap i)).val = actual U.val i := by
      intro i
      fin_cases i <;> first | exact hU | exact hOmega | exact hZero | rfl
    apply (realize_existsSuffix (m := 19) N (body.{u+1,v} K J) p).mpr
    refine ⟨w,(realize_body N q).mpr ⟨?_,?_⟩⟩
    · exact PureSatisfactionSource.actual_body hV N hmem hCol hSep hpair hUnion
        (hOmega ▸ (p 1).property) U (q ∘ pureMap) hq
    · apply (PureDefCertificate.realize_formula_iff_DefZF (interpretation U.val) rfl
        hV N hmem (q ∘ defMap) ?_).mpr hD
      intro i
      fin_cases i <;> first | exact hU | exact hZero | rfl

end OneYTruth.PureDefSource

#print axioms OneYTruth.PureDefSource.query_isSigmaOne
#print axioms OneYTruth.PureDefSource.query_sound
#print axioms OneYTruth.PureDefSource.realize_query_iff
