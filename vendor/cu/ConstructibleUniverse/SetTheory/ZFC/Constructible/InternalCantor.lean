/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalSchroederBernstein

/-!
# Cantor's theorem inside the constructible universe

The diagonal subset is produced by Full Separation in `L`.  Consequently the
argument rules out an internally represented bijection between a set and its
internal powerset; it does not appeal to ambient cardinal arithmetic.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

/-- With assignment `[graph, x]`, there is a graph value `y` at `x` and
`x` is not a member of `y`. -/
def cantorDiagonalPredicate : FOFormula 2 :=
  .ex (.conj
    (graphValueAt
      (0 : Fin 2).castSucc (1 : Fin 2).castSucc (Fin.last 2))
    (.neg (.mem (1 : Fin 2).castSucc (Fin.last 2))))

private theorem cantorDiagonal_assignment
    (graph x : Constructible.Model.LCarrier.{u}) :
    snoc ![graph] x = ![graph, x] := by
  funext i
  fin_cases i <;> rfl

private theorem cantorDiagonal_witness_assignment
    (graph x y : Constructible.Model.LCarrier.{u}) :
    snoc ![graph, x] y = ![graph, x, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_cantorDiagonalPredicate
    (graph x : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      cantorDiagonalPredicate (snoc ![graph] x) ↔
        ∃ y : Constructible.Model.LCarrier.{u},
          GraphValue Constructible.Model.lCarrierMem graph x y ∧
            x.1 ∉ y.1 := by
  rw [cantorDiagonal_assignment]
  simp only [cantorDiagonalPredicate, FOFormula.Satisfies,
    satisfies_graphValueAt]
  apply exists_congr
  intro y
  rw [cantorDiagonal_witness_assignment]
  rfl

/-! ## The singleton injection into an internal powerset -/

/-- Layout `[base, power, x, y]`: `x ∈ base`, `y ∈ power`, and
`y = {x}` internally. -/
def singletonInjectionPredicate : FOFormula 4 :=
  .conj (.mem (2 : Fin 4) (0 : Fin 4))
    (.conj (.mem (3 : Fin 4) (1 : Fin 4))
      (singletonAt (3 : Fin 4) (2 : Fin 4)))

private theorem singletonInjection_assignment
    (base power x y : Constructible.Model.LCarrier.{u}) :
    snoc (snoc ![base, power] x) y = ![base, power, x, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_singletonInjectionPredicate
    (base power x y : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      singletonInjectionPredicate
      (snoc (snoc ![base, power] x) y) ↔
        x.1 ∈ base.1 ∧ y.1 ∈ power.1 ∧
          IsSingletonOf Constructible.Model.lCarrierMem y x := by
  rw [singletonInjection_assignment]
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (satisfies_singletonAt Constructible.Model.lCarrierMem
      (3 : Fin 4) (2 : Fin 4) ![base, power, x, y]))

/-- Every set internally injects into its internal powerset by singletons. -/
theorem injects_powerSet_lCarrier
    {base power : Constructible.Model.LCarrier.{u}}
    (hpower : IsPowerSetOf Constructible.Model.lCarrierMem base power) :
    Injects Constructible.Model.lCarrierMem base power := by
  let container := unionLCarrier base power
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      singletonInjectionPredicate ![base, power] container with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : ∀ x y : Constructible.Model.LCarrier.{u},
      GraphValue Constructible.Model.lCarrierMem graph x y ↔
        x.1 ∈ base.1 ∧ y.1 ∈ power.1 ∧
          IsSingletonOf Constructible.Model.lCarrierMem y x := by
    intro x y
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨_hxContainer, _hyContainer, hformula⟩
      exact (satisfies_singletonInjectionPredicate base power x y).mp
        hformula
    · intro hformula
      refine ⟨?_, ?_, ?_⟩
      · exact (mem_unionLCarrier_iff base power x).mpr
          (Or.inl hformula.1)
      · exact (mem_unionLCarrier_iff base power y).mpr
          (Or.inr hformula.2.1)
      · exact (satisfies_singletonInjectionPredicate base power x y).mpr
          hformula
  refine ⟨graph, ?_, ?_, ?_⟩
  · intro pair hpair
    rcases hsupport pair hpair with
      ⟨x, y, _hxContainer, _hyContainer, hpairEq, hformula⟩
    have hsemantic :=
      (satisfies_singletonInjectionPredicate base power x y).mp hformula
    exact ⟨x, hsemantic.1, y, hsemantic.2.1,
      (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq⟩
  · intro x hx
    let singleton : Constructible.Model.LCarrier.{u} :=
      ⟨({x.1} : ZFSet.{u}), Constructible.singleton_mem_L x.2⟩
    have hsingleton :
        IsSingletonOf Constructible.Model.lCarrierMem singleton x := by
      constructor
      · change x.1 ∈ ({x.1} : ZFSet.{u})
        exact ZFSet.mem_singleton.mpr rfl
      · intro z hz
        apply Subtype.ext
        change z.1 ∈ ({x.1} : ZFSet.{u}) at hz
        exact ZFSet.mem_singleton.mp hz
    have hsingletonSubset :
        IsSubsetOf Constructible.Model.lCarrierMem singleton base := by
      intro z hz
      have hzx : z = x := hsingleton.2 z hz
      simpa only [hzx] using hx
    have hsingletonPower : singleton.1 ∈ power.1 :=
      (hpower singleton).mpr hsingletonSubset
    refine ⟨singleton, hsingletonPower,
      (hvalue x singleton).mpr ⟨hx, hsingletonPower, hsingleton⟩, ?_⟩
    intro y _hy hyValue
    have hySingleton := (hvalue x y).mp hyValue |>.2.2
    apply Constructible.Model.lCarrier_extensionality
    intro z
    constructor
    · intro hzy
      have hzx : z = x := hySingleton.2 z hzy
      subst z
      exact hsingleton.1
    · intro hzSingleton
      have hzx : z = x := hsingleton.2 z hzSingleton
      subst z
      exact hySingleton.1
  · intro y _hy x _hx hxy z _hz hzy
    have hySingletonX := (hvalue x y).mp hxy |>.2.2
    have hySingletonZ := (hvalue z y).mp hzy |>.2.2
    exact (hySingletonZ.2 x hySingletonX.1).symm

/--
Cantor's diagonal argument in `LCarrier`: an internal powerset is not
internally equinumerous with its base.
-/
theorem not_equinumerous_powerSet_lCarrier
    {base power : Constructible.Model.LCarrier.{u}}
    (hpower : IsPowerSetOf Constructible.Model.lCarrierMem base power) :
    ¬Equinumerous Constructible.Model.lCarrierMem base power := by
  rintro ⟨graph, hgraph⟩
  rcases Constructible.Model.exists_separationLCarrier
      cantorDiagonalPredicate ![graph] base with ⟨diagonal, hdiagonal⟩
  have hdiagonalSubset :
      IsSubsetOf Constructible.Model.lCarrierMem diagonal base := by
    intro x hx
    exact (hdiagonal x).mp hx |>.1
  have hdiagonalPower : diagonal.1 ∈ power.1 :=
    (hpower diagonal).mpr hdiagonalSubset
  rcases hgraph.2.2 diagonal hdiagonalPower with
    ⟨x, hxBase, hxDiagonal, _hxUnique⟩
  have hmembership : x.1 ∈ diagonal.1 ↔ x.1 ∉ diagonal.1 := by
    constructor
    · intro hxMem
      rcases (hdiagonal x).mp hxMem with ⟨_hxBase, hpredicate⟩
      rcases (satisfies_cantorDiagonalPredicate graph x).mp
          hpredicate with ⟨image, hxImage, hxNotImage⟩
      rcases hgraph.2.1 x hxBase with
        ⟨value, hvaluePower, hxValue, hvalueUnique⟩
      have himageEq : image = value :=
        hvalueUnique image
          ((hgraph.1.graphValue_mem_lCarrier hxImage).2) hxImage
      have hdiagonalEq : diagonal = value :=
        hvalueUnique diagonal hdiagonalPower hxDiagonal
      have himageDiagonal : image = diagonal :=
        himageEq.trans hdiagonalEq.symm
      simpa only [himageDiagonal] using hxNotImage
    · intro hxNotMem
      apply (hdiagonal x).mpr
      refine ⟨hxBase, ?_⟩
      exact (satisfies_cantorDiagonalPredicate graph x).mpr
        ⟨diagonal, hxDiagonal, hxNotMem⟩
  by_cases hx : x.1 ∈ diagonal.1
  · exact (hmembership.mp hx) hx
  · exact hx (hmembership.mpr hx)

/-- No internal injection can send an internal powerset back into its base. -/
theorem not_injects_powerSet_lCarrier
    {base power : Constructible.Model.LCarrier.{u}}
    (hpower : IsPowerSetOf Constructible.Model.lCarrierMem base power) :
    ¬Injects Constructible.Model.lCarrierMem power base := by
  intro hback
  exact not_equinumerous_powerSet_lCarrier hpower
    (injects_antisymm_lCarrier
      (injects_powerSet_lCarrier hpower) hback)

end Constructible.ContinuumFormula
