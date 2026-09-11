/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.MostowskiElementarity

/-!
# Definability and the Mostowski collapse

This file proves the successor-step compatibility needed by constructible
condensation.  If a set-sized membership structure is fully elementary in a
transitive ambient set, then its Mostowski collapse commutes with `DefZF` on
every argument for which both the argument and its definable powerset belong
to the small structure.

The finite tuple of parameters occurring in the definition of a subset is
not assumed to lie in the small structure.  Instead it is bound in one
first-order formula.  Full elementarity pulls witnesses into the small
structure, after which invariance of satisfaction under the collapse applies.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

namespace Model

@[simp]
theorem satisfiesIn_disj_iff (M : Set ZFSet.{u}) {n : Nat}
    (phi psi : FOFormula n) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.disj phi psi) s <->
      SatisfiesIn M phi s ∨ SatisfiesIn M psi s := by
  classical
  simp only [FOFormula.disj, SatisfiesIn]
  tauto

@[simp]
theorem satisfiesIn_imp_iff (M : Set ZFSet.{u}) {n : Nat}
    (phi psi : FOFormula n) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.imp phi psi) s <->
      (SatisfiesIn M phi s -> SatisfiesIn M psi s) := by
  classical
  simp only [FOFormula.imp, satisfiesIn_disj_iff, SatisfiesIn]
  tauto

@[simp]
theorem satisfiesIn_biimp_iff (M : Set ZFSet.{u}) {n : Nat}
    (phi psi : FOFormula n) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp phi psi) s <->
      (SatisfiesIn M phi s <-> SatisfiesIn M psi s) := by
  classical
  simp only [FOFormula.biimp, SatisfiesIn, satisfiesIn_imp_iff]
  tauto

@[simp]
theorem satisfiesIn_boundedEx_iff (M : Set ZFSet.{u}) {n : Nat}
    (i : Fin n) (phi : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.boundedEx i phi) s <->
      ∃ x : ZFSet.{u}, x ∈ M ∧ x ∈ s i ∧
        SatisfiesIn M phi (snoc s x) := by
  simp [FOFormula.boundedEx]

@[simp]
theorem satisfiesIn_boundedAll_iff (M : Set ZFSet.{u}) {n : Nat}
    (i : Fin n) (phi : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.boundedAll i phi) s <->
      ∀ x : ZFSet.{u}, x ∈ M -> x ∈ s i ->
        SatisfiesIn M phi (snoc s x) := by
  classical
  simp only [FOFormula.boundedAll, SatisfiesIn,
    satisfiesIn_boundedEx_iff]
  constructor
  · intro h x hxM hxi
    by_contra hx
    exact h ⟨x, hxM, hxi, hx⟩
  · intro h hex
    rcases hex with ⟨x, hxM, hxi, hx⟩
    exact hx (h x hxM hxi)

/-- Relativizing every quantifier to `a` inside a class `M` is satisfaction
over the external intersection `M ∩ a`. -/
theorem satisfiesIn_toFO_relativize_iff (M : Set ZFSet.{u})
    (a : ZFSet.{u}) {n : Nat} (phi : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (Delta0Formula.relativize phi).toFO
        (tupleCons a s) <->
      SatisfiesIn (M ∩ (a : Set ZFSet.{u})) phi s := by
  induction phi with
  | mem i j => rfl
  | eq i j => rfl
  | neg phi ih =>
      simpa [Delta0Formula.relativize, Delta0Formula.toFO] using
        not_congr (ih s)
  | conj phi psi ihPhi ihPsi =>
      simpa [Delta0Formula.relativize, Delta0Formula.toFO] using
        and_congr (ihPhi s) (ihPsi s)
  | ex phi ih =>
      simp only [Delta0Formula.relativize, Delta0Formula.toFO,
        FOFormula.boundedEx, SatisfiesIn, snoc_tupleCons, ih,
        tupleCons_zero, snoc_last, snoc_castSucc]
      constructor
      · rintro ⟨x, hxM, hxa, hx⟩
        exact ⟨x, ⟨hxM, hxa⟩, hx⟩
      · rintro ⟨x, ⟨hxM, hxa⟩, hx⟩
        exact ⟨x, hxM, hxa, hx⟩

/-- In a transitive ambient set containing `a`, the intersection in the
previous theorem is exactly the genuine carrier of `a`. -/
theorem satisfiesIn_toFO_relativize_of_isTransitive
    {M a : ZFSet.{u}} (hM : M.IsTransitive) (ha : a ∈ M)
    {n : Nat} (phi : FOFormula n) (s : Tuple (ZFCarrier a) n) :
    SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.relativize phi).toFO
        (tupleCons a (Delta0Formula.val s)) <->
      FOFormula.Satisfies (zfCarrierMem a) phi s := by
  rw [satisfiesIn_toFO_relativize_iff]
  have hinter : (M : Set ZFSet.{u}) ∩ (a : Set ZFSet.{u}) =
      (a : Set ZFSet.{u}) := by
    ext x
    constructor
    · exact fun hx => hx.2
    · intro hxa
      exact ⟨hM.mem_trans hxa ha, hxa⟩
  rw [hinter]
  exact (satisfies_subtype_iff_satisfiesIn
    (a : Set ZFSet.{u}) phi s).symm

end Model

/-! ## One formula saying that a set is a definable section -/

/-- Insert the coordinate for the defined subset between the bound `a` and
the original assignment. -/
def sectionRelativizeRename {n : Nat} :
    Fin (n + 2) -> Fin (n + 3) :=
  Fin.cases 0 (fun i => i.succ.succ)

private theorem sectionRelativizeRename_assignment {n : Nat}
    (a y x : ZFSet.{u}) (s : Tuple ZFSet.{u} n) :
    (fun i =>
      snoc (tupleCons a (tupleCons y s)) x
        (sectionRelativizeRename i)) =
      tupleCons a (snoc s x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [sectionRelativizeRename]
  · simp [sectionRelativizeRename]

/-- `subsetDefinitionFormula phi` has free layout `[a, y, params...]` and
asserts that `y` is the section of `phi` over the structure carried by `a`.
-/
def subsetDefinitionFormula {n : Nat} (phi : FOFormula (n + 1)) :
    FOFormula (n + 2) :=
  FOFormula.boundedAll (0 : Fin (n + 2))
    (FOFormula.biimp
      (.mem (Fin.last (n + 2)) (1 : Fin (n + 2)).castSucc)
      (FOFormula.rename sectionRelativizeRename
        (Delta0Formula.relativize phi).toFO))

/-- Exact semantics of `subsetDefinitionFormula` in a transitive ambient
set. -/
theorem satisfiesIn_subsetDefinitionFormula_iff
    {M a y : ZFSet.{u}} (hM : M.IsTransitive) (ha : a ∈ M)
    {n : Nat} (phi : FOFormula (n + 1))
    (s : Tuple (ZFCarrier a) n) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        (subsetDefinitionFormula phi)
        (tupleCons a (tupleCons y (Delta0Formula.val s))) <->
      ∀ x : ZFCarrier a,
        x.1 ∈ y <->
          FOFormula.Satisfies (zfCarrierMem a) phi (snoc s x) := by
  classical
  simp only [subsetDefinitionFormula, Model.satisfiesIn_boundedAll_iff,
    Model.satisfiesIn_biimp_iff, Model.SatisfiesIn,
    snoc_last, snoc_castSucc, tupleCons_zero,
    Model.satisfiesIn_rename, sectionRelativizeRename_assignment]
  constructor
  · intro h x
    have hxM : x.1 ∈ M := hM.mem_trans x.2 ha
    have hx := h x.1 hxM x.2
    change x.1 ∈ y <->
      Model.SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.relativize phi).toFO
        (tupleCons a (snoc (Delta0Formula.val s) x.1)) at hx
    have hrel := Model.satisfiesIn_toFO_relativize_of_isTransitive
      hM ha phi (snoc s x)
    have hrel' :
        Model.SatisfiesIn (M : Set ZFSet.{u})
          (Delta0Formula.relativize phi).toFO
          (tupleCons a (snoc (Delta0Formula.val s) x.1)) <->
        FOFormula.Satisfies (zfCarrierMem a) phi (snoc s x) := by
      simpa only [Delta0Formula.val_snoc] using hrel
    exact hx.trans hrel'
  · intro h x hxM hxa
    let xa : ZFCarrier a := ⟨x, hxa⟩
    change x ∈ y <->
      Model.SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.relativize phi).toFO
        (tupleCons a (snoc (Delta0Formula.val s) x))
    have hrel := Model.satisfiesIn_toFO_relativize_of_isTransitive
      hM ha phi (snoc s xa)
    have hrel' :
        Model.SatisfiesIn (M : Set ZFSet.{u})
          (Delta0Formula.relativize phi).toFO
          (tupleCons a (snoc (Delta0Formula.val s) x)) <->
        FOFormula.Satisfies (zfCarrierMem a) phi (snoc s xa) := by
      simpa only [xa, Delta0Formula.val_snoc] using hrel
    exact (h xa).trans hrel'.symm

/-! ## Binding all finite parameters in one object-language formula -/

/-- Bind all coordinates after the first two, requiring every witness to be
a member of coordinate zero. -/
def boundedExistsTail : (n : Nat) -> FOFormula (n + 2) -> FOFormula 2
  | 0, phi => phi
  | n + 1, phi =>
      boundedExistsTail n
        (FOFormula.boundedEx (0 : Fin (n + 2)) phi)

private theorem tuple_snoc_eta {A : Type u} {n : Nat}
    (s : Tuple A (n + 1)) :
    snoc (fun i => s i.castSucc) (s (Fin.last n)) = s := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- Semantics of binding a finite tail of parameters. -/
theorem satisfiesIn_boundedExistsTail_iff
    (M : Set ZFSet.{u}) (a y : ZFSet.{u}) {n : Nat}
    (phi : FOFormula (n + 2)) :
    Model.SatisfiesIn M (boundedExistsTail n phi) ![a, y] <->
      ∃ s : Tuple ZFSet.{u} n,
        (∀ i, s i ∈ M ∧ s i ∈ a) ∧
        Model.SatisfiesIn M phi
          (tupleCons a (tupleCons y s)) := by
  induction n with
  | zero =>
      rw [boundedExistsTail]
      constructor
      · intro h
        refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · convert h using 1
          funext i
          fin_cases i <;> rfl
      · rintro ⟨s, _hs, h⟩
        convert h using 1
        funext i
        fin_cases i <;> rfl
  | succ n ih =>
      rw [boundedExistsTail]
      rw [ih]
      simp only [Model.satisfiesIn_boundedEx_iff, tupleCons_zero]
      constructor
      · rintro ⟨s, hs, x, hxM, hxa, hx⟩
        refine ⟨snoc s x, ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using And.intro hxM hxa
          · simpa using hs j
        · simpa only [snoc_tupleCons] using hx
      · rintro ⟨s, hs, hphi⟩
        let pref : Tuple ZFSet.{u} n := fun i => s i.castSucc
        let x : ZFSet.{u} := s (Fin.last n)
        refine ⟨pref, ?_, x, ?_, ?_, ?_⟩
        · intro i
          exact hs i.castSucc
        · exact (hs (Fin.last n)).1
        · exact (hs (Fin.last n)).2
        · have heta : snoc pref x = s := tuple_snoc_eta s
          simpa only [snoc_tupleCons, heta, pref, x] using hphi

/-- Bind all parameters of a section definition.  The only free variables
are `[a, y]`. -/
def existsParametersDefinitionFormula {n : Nat}
    (phi : FOFormula (n + 1)) : FOFormula 2 :=
  boundedExistsTail n (subsetDefinitionFormula phi)

/-! ## Asking for a defined subset inside `DefZF a` -/

/-- Move the defined-set coordinate to the final position.  The source layout
is `[a, y, params...]`; the target layout is `[a, DefZF a, params..., y]`. -/
def definedSubsetWitnessRename {n : Nat} :
    Fin (n + 2) -> Fin (n + 3) :=
  Fin.cases 0
    (fun i => Fin.cases (Fin.last (n + 2))
      (fun j => (j.succ.succ).castSucc) i)

private theorem definedSubsetWitnessRename_assignment {n : Nat}
    (a d y : ZFSet.{u}) (s : Tuple ZFSet.{u} n) :
    (fun i =>
      snoc (tupleCons a (tupleCons d s)) y
        (definedSubsetWitnessRename i)) =
      tupleCons a (tupleCons y s) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [definedSubsetWitnessRename]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp only [definedSubsetWitnessRename, Fin.cases_succ,
        Fin.cases_zero, snoc_last, tupleCons_succ, tupleCons_zero]
    · simp [definedSubsetWitnessRename]

/-- Free layout `[a, d, params...]`.  This formula says that some `y ∈ d`
is the subset of `a` defined by `phi` and the displayed parameters. -/
def existsDefinedSubsetFormula {n : Nat}
    (phi : FOFormula (n + 1)) : FOFormula (n + 2) :=
  FOFormula.boundedEx (1 : Fin (n + 2))
    (FOFormula.rename definedSubsetWitnessRename
      (subsetDefinitionFormula phi))

theorem satisfiesIn_existsDefinedSubsetFormula_iff
    (M : Set ZFSet.{u}) (a d : ZFSet.{u}) {n : Nat}
    (phi : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (existsDefinedSubsetFormula phi)
        (tupleCons a (tupleCons d s)) <->
      ∃ y : ZFSet.{u}, y ∈ M ∧ y ∈ d ∧
        Model.SatisfiesIn M (subsetDefinitionFormula phi)
          (tupleCons a (tupleCons y s)) := by
  simp only [existsDefinedSubsetFormula,
    Model.satisfiesIn_boundedEx_iff, Model.satisfiesIn_rename,
    definedSubsetWitnessRename_assignment]
  change (∃ y : ZFSet.{u}, y ∈ M ∧ y ∈ d ∧
      Model.SatisfiesIn M (subsetDefinitionFormula phi)
        (tupleCons a (tupleCons y s))) <-> _
  rfl

namespace MostowskiCollapse

/-- Raw-tuple form of satisfaction invariance under the collapse. -/
theorem satisfiesIn_collapse_iff_raw {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain) {n : Nat}
    (phi : FOFormula n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ domain) :
    Model.SatisfiesIn (domain : Set ZFSet.{u}) phi s <->
      Model.SatisfiesIn (range domain : Set ZFSet.{u}) phi
        (fun i => collapse domain (s i)) := by
  let sDomain : Tuple {x : ZFSet.{u} // x ∈ domain} n :=
    fun i => ⟨s i, hs i⟩
  simpa only [sDomain] using
    (satisfiesIn_collapse_iff hextensional phi sDomain)

/-- A section definition whose parameters belong to the collapse domain
transports to the corresponding section definition over the collapsed bound.
-/
theorem exists_collapsedParameters_section
    {domain a y : ZFSet.{u}} (hextensional : IsExtensional domain)
    (ha : a ∈ domain) (hy : y ∈ domain)
    {n : Nat} (phi : FOFormula (n + 1))
    (s : Tuple (ZFCarrier a) n)
    (hs : ∀ i, (s i).1 ∈ domain)
    (hsection :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        (subsetDefinitionFormula phi)
        (tupleCons a (tupleCons y (Delta0Formula.val s)))) :
    ∃ collapsedParams : Tuple (ZFCarrier (collapse domain a)) n,
      (∀ i, (collapsedParams i).1 = collapse domain (s i).1) ∧
      (∀ x : ZFCarrier (collapse domain a),
        x.1 ∈ collapse domain y <->
          FOFormula.Satisfies
            (zfCarrierMem (collapse domain a)) phi
            (snoc collapsedParams x)) := by
  let collapsedParams : Tuple (ZFCarrier (collapse domain a)) n :=
    fun i => ⟨collapse domain (s i).1,
      mem_collapse_iff.mpr ⟨(s i).1, (s i).2, hs i, rfl⟩⟩
  have hentries :
      ∀ i, tupleCons a (tupleCons y (Delta0Formula.val s)) i ∈ domain := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [tupleCons_zero] using ha
    · refine Fin.cases ?_ (fun k => ?_) j
      · simpa only [tupleCons_succ, tupleCons_zero] using hy
      · simp only [tupleCons_succ]
        exact hs k
  have hcollapsed :=
    (satisfiesIn_collapse_iff_raw hextensional
      (subsetDefinitionFormula phi)
      (tupleCons a (tupleCons y (Delta0Formula.val s))) hentries).mp
      hsection
  have hassignment :
      (fun i => collapse domain
        (tupleCons a (tupleCons y (Delta0Formula.val s)) i)) =
      tupleCons (collapse domain a)
        (tupleCons (collapse domain y)
          (Delta0Formula.val collapsedParams)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · rfl
  rw [hassignment] at hcollapsed
  have haRange : collapse domain a ∈ range domain :=
    mem_range_iff.mpr ⟨a, ha, rfl⟩
  have hsemantic :=
    (satisfiesIn_subsetDefinitionFormula_iff
      (range_isTransitive domain) haRange phi collapsedParams).mp
      hcollapsed
  exact ⟨collapsedParams, fun i => rfl, hsemantic⟩

/-- The restricted collapse is monotone in its second argument. -/
theorem collapse_mono {domain x y : ZFSet.{u}} (hxy : x ⊆ y) :
    collapse domain x ⊆ collapse domain y := by
  intro z hz
  rcases mem_collapse_iff.mp hz with ⟨w, hwx, hwDomain, rfl⟩
  exact mem_collapse_iff.mpr ⟨w, hxy hwx, hwDomain, rfl⟩

/--
The successor step of condensation: a fully elementary set-sized membership
structure inside a transitive ambient set commutes with `DefZF` under its
Mostowski collapse.

The hypotheses that both `a` and `DefZF a` belong to `domain` are essential:
they make the relevant section-existence statements available as formulas
with parameters from the elementary substructure.
-/
theorem collapse_DefZF_eq_DefZF_collapse
    {domain ambient a : ZFSet.{u}}
    (hsubset : (domain : Set ZFSet.{u}) ⊆
      (ambient : Set ZFSet.{u}))
    (hambient : ambient.IsTransitive)
    (habsolute : SatisfactionAbsolute
      (domain : Set ZFSet.{u}) (ambient : Set ZFSet.{u}))
    (ha : a ∈ domain) (hDef : DefZF a ∈ domain) :
    collapse domain (DefZF a) = DefZF (collapse domain a) := by
  classical
  have haAmbient : a ∈ ambient := hsubset ha
  have hDefAmbient : DefZF a ∈ ambient := hsubset hDef
  have hclose : ClosesWithinAll
      (domain : Set ZFSet.{u}) (ambient : Set ZFSet.{u}) :=
    closesWithinAll_of_satisfactionAbsolute habsolute
  have hextensional : IsExtensional domain := by
    intro x hx y hy hsame
    exact restricted_extensionality_of_closesWithinAll hsubset
      (fun w hw z hzw => hambient.mem_trans hzw hw)
      hclose hx hy hsame
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    rcases mem_collapse_iff.mp hz with
      ⟨y, hyDef, hyDomain, hyCollapse⟩
    rcases mem_DefZF_iff_exists_satisfies.mp hyDef with
      ⟨hya, n, s, phi, hphi⟩
    have hsectionAmbient :
        Model.SatisfiesIn (ambient : Set ZFSet.{u})
          (subsetDefinitionFormula phi)
          (tupleCons a
            (tupleCons y (Delta0Formula.val s))) :=
      (satisfiesIn_subsetDefinitionFormula_iff
        hambient haAmbient phi s).mpr hphi
    have hparameterAmbient :
        ∀ i, Delta0Formula.val s i ∈ (ambient : Set ZFSet.{u}) ∧
          Delta0Formula.val s i ∈ a := by
      intro i
      exact ⟨hambient.mem_trans (s i).2 haAmbient, (s i).2⟩
    have hexAmbient :
        Model.SatisfiesIn (ambient : Set ZFSet.{u})
          (existsParametersDefinitionFormula phi) ![a, y] :=
      (satisfiesIn_boundedExistsTail_iff
        (ambient : Set ZFSet.{u}) a y
        (subsetDefinitionFormula phi)).mpr
        ⟨Delta0Formula.val s, hparameterAmbient, hsectionAmbient⟩
    have hpairDomain : ∀ i, ![a, y] i ∈ domain := by
      intro i
      fin_cases i
      · exact ha
      · exact hyDomain
    have hexDomain :
        Model.SatisfiesIn (domain : Set ZFSet.{u})
          (existsParametersDefinitionFormula phi) ![a, y] :=
      (habsolute (existsParametersDefinitionFormula phi)
        ![a, y] hpairDomain).mpr hexAmbient
    rcases (satisfiesIn_boundedExistsTail_iff
      (domain : Set ZFSet.{u}) a y
      (subsetDefinitionFormula phi)).mp hexDomain with
      ⟨rawParams, hrawParams, hsectionDomain⟩
    let params : Tuple (ZFCarrier a) n :=
      fun i => ⟨rawParams i, (hrawParams i).2⟩
    have hparamsDomain : ∀ i, (params i).1 ∈ domain :=
      fun i => (hrawParams i).1
    have hparamsVal : Delta0Formula.val params = rawParams := by
      funext i
      rfl
    rw [← hparamsVal] at hsectionDomain
    rcases exists_collapsedParameters_section hextensional ha hyDomain
      phi params hparamsDomain hsectionDomain with
      ⟨collapsedParams, _hcollapsedParams, hcollapsedSection⟩
    rw [← hyCollapse]
    apply mem_DefZF_iff_exists_satisfies.mpr
    refine ⟨collapse_mono hya, n, collapsedParams, phi, ?_⟩
    exact hcollapsedSection
  · intro hz
    rcases mem_DefZF_iff_exists_satisfies.mp hz with
      ⟨hza, n, collapsedParams, phi, hphi⟩
    have hpreimages : ∀ i,
        ∃ x : ZFSet.{u}, x ∈ a ∧ x ∈ domain ∧
          collapse domain x = (collapsedParams i).1 := by
      intro i
      exact mem_collapse_iff.mp (collapsedParams i).2
    choose rawParams hrawParamsA hrawParamsDomain
      hrawParamsCollapse using hpreimages
    let params : Tuple (ZFCarrier a) n :=
      fun i => ⟨rawParams i, hrawParamsA i⟩
    let definingClass : Set (ZFCarrier a) :=
      {x | FOFormula.Satisfies (zfCarrierMem a) phi (snoc params x)}
    let y0 : ZFSet.{u} := representZFSubset a definingClass
    have hy0Section : ∀ x : ZFCarrier a,
        x.1 ∈ y0 <->
          FOFormula.Satisfies (zfCarrierMem a) phi (snoc params x) := by
      intro x
      change x.1 ∈ representZFSubset a definingClass <-> _
      rw [mem_representZFSubset_iff]
      constructor
      · rintro ⟨_hxa, hx⟩
        exact hx
      · intro hx
        exact ⟨x.2, hx⟩
    have hy0Def : y0 ∈ DefZF a :=
      mem_DefZF_iff_exists_satisfies.mpr
        ⟨representZFSubset_subset a definingClass,
          n, params, phi, hy0Section⟩
    have hy0Ambient : y0 ∈ ambient :=
      hambient.mem_trans hy0Def hDefAmbient
    have hsectionAmbient :
        Model.SatisfiesIn (ambient : Set ZFSet.{u})
          (subsetDefinitionFormula phi)
          (tupleCons a
            (tupleCons y0 (Delta0Formula.val params))) :=
      (satisfiesIn_subsetDefinitionFormula_iff
        hambient haAmbient phi params).mpr hy0Section
    have hexAmbient :
        Model.SatisfiesIn (ambient : Set ZFSet.{u})
          (existsDefinedSubsetFormula phi)
          (tupleCons a
            (tupleCons (DefZF a) (Delta0Formula.val params))) :=
      (satisfiesIn_existsDefinedSubsetFormula_iff
        (ambient : Set ZFSet.{u}) a (DefZF a) phi
        (Delta0Formula.val params)).mpr
        ⟨y0, hy0Ambient, hy0Def, hsectionAmbient⟩
    have hallDomain : ∀ i,
        tupleCons a (tupleCons (DefZF a)
          (Delta0Formula.val params)) i ∈ domain := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [tupleCons_zero] using ha
      · refine Fin.cases ?_ (fun k => ?_) j
        · simpa only [tupleCons_succ, tupleCons_zero] using hDef
        · simp only [tupleCons_succ]
          exact hrawParamsDomain k
    have hexDomain :
        Model.SatisfiesIn (domain : Set ZFSet.{u})
          (existsDefinedSubsetFormula phi)
          (tupleCons a
            (tupleCons (DefZF a) (Delta0Formula.val params))) :=
      (habsolute (existsDefinedSubsetFormula phi)
        (tupleCons a
          (tupleCons (DefZF a) (Delta0Formula.val params)))
        hallDomain).mpr hexAmbient
    rcases (satisfiesIn_existsDefinedSubsetFormula_iff
      (domain : Set ZFSet.{u}) a (DefZF a) phi
      (Delta0Formula.val params)).mp hexDomain with
      ⟨y, hyDomain, hyDef, hsectionDomain⟩
    rcases exists_collapsedParameters_section hextensional ha hyDomain
      phi params hrawParamsDomain hsectionDomain with
      ⟨transportedParams, htransportedParams, htransportedSection⟩
    have hparamsEq : transportedParams = collapsedParams := by
      funext i
      apply Subtype.ext
      exact (htransportedParams i).trans (hrawParamsCollapse i)
    apply mem_collapse_iff.mpr
    refine ⟨y, hyDef, hyDomain, ?_⟩
    apply ZFSet.ext
    intro w
    by_cases hwa : w ∈ collapse domain a
    · let wa : ZFCarrier (collapse domain a) := ⟨w, hwa⟩
      have hleft := htransportedSection wa
      have hright := hphi wa
      rw [hparamsEq] at hleft
      exact hleft.trans hright.symm
    · constructor
      · intro hwy
        exact (hwa (collapse_mono
          (mem_DefZF_iff_exists_satisfies.mp hyDef).1 hwy)).elim
      · intro hwz
        exact (hwa (hza hwz)).elim

end MostowskiCollapse

end

end Constructible
