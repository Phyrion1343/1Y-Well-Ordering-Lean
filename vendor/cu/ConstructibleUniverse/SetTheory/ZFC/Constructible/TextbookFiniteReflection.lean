/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteFragmentCollapse
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.MostowskiElementarity
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookFiniteSkolemCardinal

/-!
# Finite transitive reflection by the textbook Skolem construction

This file assembles the non-cardinal part of Theorem 3 in Section 6.3 of
Wang Fangting, *Axiomatic Set Theory*.

For a finite list of sentences, the Skolem family contains every existential
subformula in the list and also the distinguishing-member matrix used in the
Extensionality argument.  Its omega closure is a set-sized substructure of the
ambient transitive set.  Restricted Extensionality gives the Mostowski
collapse, whose range is transitive.  The collapse is the textbook recursion

`f(u) = {f(v) | v in domain intersection u}`.

Consequently the collapse fixes every member of a transitive seed, contains
that seed, and agrees with the ambient structure on every listed sentence.
No full-elementarity or Condensation hypothesis occurs here.  The cardinal
estimate `|z| <= max(aleph_0, |seed|)` is deliberately proved in the next
cardinal layer rather than hidden in this structural theorem.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

/-- The finite Skolem family for a list of sentences, enlarged by exactly the
distinguishing-member matrix needed to prove Extensionality of the hull. -/
def textbookFiniteFragmentMatrices
    (sentences : List (FOFormula 0)) : List ExistentialMatrix :=
  sentences.flatMap existentialMatrices ++
    existentialMatrices distinguishingMemberFormula

/-- Every listed sentence is covered by the finite Skolem family. -/
theorem coversExistentialSubformulas_textbookFiniteFragmentMatrices_of_mem
    (sentences : List (FOFormula 0)) {sentence : FOFormula 0}
    (hsentence : sentence ∈ sentences) :
    CoversExistentialSubformulas
      (textbookFiniteFragmentMatrices sentences) sentence := by
  apply CoversExistentialSubformulas.mono
    (hcover := coversExistentialSubformulas_existentialMatrices sentence)
  intro matrix hmatrix
  exact List.mem_append_left _
    (List.mem_flatMap_of_mem hsentence hmatrix)

/-- The same family covers the distinguishing-member formula. -/
theorem coversExistentialSubformulas_distinguishingMember
    (sentences : List (FOFormula 0)) :
    CoversExistentialSubformulas
      (textbookFiniteFragmentMatrices sentences)
      distinguishingMemberFormula := by
  apply CoversExistentialSubformulas.mono
    (hcover := coversExistentialSubformulas_existentialMatrices
      distinguishingMemberFormula)
  intro matrix hmatrix
  exact List.mem_append_right _ hmatrix

/-- The set-sized omega Skolem closure attached to a finite sentence list. -/
noncomputable def textbookFiniteFragmentHull
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (sentences : List (FOFormula 0)) (seed : ZFSubset U) : ZFSet.{u} :=
  textbookSkolemOmegaUnion U default
    (textbookFiniteFragmentMatrices sentences) seed

/-- The finite-fragment hull contains its seed. -/
theorem seed_subset_textbookFiniteFragmentHull
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (sentences : List (FOFormula 0)) (seed : ZFSubset U) :
    seed.1 ⊆ textbookFiniteFragmentHull U default sentences seed := by
  exact seed_subset_textbookSkolemOmegaUnion U default
    (textbookFiniteFragmentMatrices sentences) seed

/-- The finite-fragment hull remains inside the ambient set. -/
theorem textbookFiniteFragmentHull_subset
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (sentences : List (FOFormula 0)) (seed : ZFSubset U) :
    textbookFiniteFragmentHull U default sentences seed ⊆ U := by
  exact textbookSkolemOmegaUnion_subset U default
    (textbookFiniteFragmentMatrices sentences) seed

/-- Every listed sentence has the recursive Tarski--Vaught closure property
between the hull and the ambient set. -/
theorem closesWithin_textbookFiniteFragmentHull_of_mem
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (sentences : List (FOFormula 0)) (seed : ZFSubset U)
    {sentence : FOFormula 0} (hsentence : sentence ∈ sentences) :
    ClosesWithin
      (textbookFiniteFragmentHull U default sentences seed : Set ZFSet.{u})
      (U : Set ZFSet.{u}) sentence := by
  exact closesWithin_textbookSkolemOmegaUnion U default
    (textbookFiniteFragmentMatrices sentences) seed sentence
    (coversExistentialSubformulas_textbookFiniteFragmentMatrices_of_mem
      sentences hsentence)

/-- The hull also has the witness closure which makes restricted membership
Extensional. -/
theorem closesWithin_distinguishingMember_textbookFiniteFragmentHull
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (sentences : List (FOFormula 0)) (seed : ZFSubset U) :
    ClosesWithin
      (textbookFiniteFragmentHull U default sentences seed : Set ZFSet.{u})
      (U : Set ZFSet.{u}) distinguishingMemberFormula := by
  exact closesWithin_textbookSkolemOmegaUnion U default
    (textbookFiniteFragmentMatrices sentences) seed
    distinguishingMemberFormula
    (coversExistentialSubformulas_distinguishingMember sentences)

/-- Restricted membership on the finite-fragment hull is extensional. -/
theorem textbookFiniteFragmentHull_isExtensional
    (U : ZFSet.{u}) (hUTransitive : U.IsTransitive)
    (default : ZFCarrier U) (sentences : List (FOFormula 0))
    (seed : ZFSubset U) :
    MostowskiCollapse.IsExtensional
      (textbookFiniteFragmentHull U default sentences seed) := by
  apply mostowskiIsExtensional_of_closesWithin
    (textbookFiniteFragmentHull_subset U default sentences seed)
    (fun x hx z hz => hUTransitive.mem_trans hz hx)
  exact closesWithin_distinguishingMember_textbookFiniteFragmentHull
    U default sentences seed

/-- Satisfaction of a listed sentence is absolute between the hull and the
ambient set. -/
theorem satisfiesIn_textbookFiniteFragmentHull_iff_of_mem
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (sentences : List (FOFormula 0)) (seed : ZFSubset U)
    {sentence : FOFormula 0} (hsentence : sentence ∈ sentences) :
    Model.SatisfiesIn
        (textbookFiniteFragmentHull U default sentences seed : Set ZFSet.{u})
        sentence (fun i => Fin.elim0 i) ↔
      Model.SatisfiesIn (U : Set ZFSet.{u})
        sentence (fun i => Fin.elim0 i) := by
  exact satisfiesIn_textbookSkolemOmegaUnion_iff U default
    (textbookFiniteFragmentMatrices sentences) seed sentence
    (coversExistentialSubformulas_textbookFiniteFragmentMatrices_of_mem
      sentences hsentence)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

namespace MostowskiCollapse

/-- Collapsing a larger (not necessarily transitive) domain fixes every
member of a transitive seed contained in that domain.  This is the induction
used in the proof of Wang's Section 6.3, Theorem 3. -/
theorem collapse_eq_self_of_mem_of_transitive_seed
    {domain seed : ZFSet.{u}} (hseedTransitive : seed.IsTransitive)
    (hseedDomain : seed ⊆ domain) :
    ∀ x : ZFSet.{u}, x ∈ seed → collapse domain x = x := by
  intro x
  refine ZFSet.inductionOn
    (p := fun x => x ∈ seed → collapse domain x = x) x ?_
  intro x ih hxSeed
  apply ZFSet.ext
  intro z
  rw [mem_collapse_iff]
  constructor
  · rintro ⟨y, hyx, _hyDomain, hyz⟩
    have hySeed : y ∈ seed := hseedTransitive.mem_trans hyx hxSeed
    have hyFixed : collapse domain y = y := ih y hyx hySeed
    have hyEq : y = z := hyFixed.symm.trans hyz
    simpa only [hyEq] using hyx
  · intro hzx
    have hzSeed : z ∈ seed := hseedTransitive.mem_trans hzx hxSeed
    exact ⟨z, hzx, hseedDomain hzSeed, ih z hzx hzSeed⟩

/-- For a sentence, the Mostowski collapse equivalence gives exactly the
same restricted satisfaction on the domain and on its transitive range. -/
theorem satisfiesIn_range_sentence_iff_domain
    {domain : ZFSet.{u}} (hextensional : IsExtensional domain)
    (sentence : FOFormula 0) :
    Model.SatisfiesIn (range domain : Set ZFSet.{u})
        sentence (fun i => Fin.elim0 i) ↔
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        sentence (fun i => Fin.elim0 i) := by
  let emptyDomain : Tuple {x : ZFSet.{u} // x ∈ domain} 0 :=
    fun i => Fin.elim0 i
  let emptyRaw : Tuple ZFSet.{u} 0 := fun i => Fin.elim0 i
  have hcollapse := satisfiesIn_collapse_iff
    hextensional sentence emptyDomain
  have hsource : (fun i => (emptyDomain i).1) = emptyRaw :=
    Subsingleton.elim _ _
  have htarget :
      (fun i => collapse domain (emptyDomain i).1) = emptyRaw :=
    Subsingleton.elim _ _
  rw [hsource, htarget] at hcollapse
  exact hcollapse.symm

end MostowskiCollapse

/-- The transitive collapse contains the original transitive seed. -/
theorem seed_subset_textbookFiniteFragmentCollapseRange
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (sentences : List (FOFormula 0)) (seed : ZFSubset U)
    (hseedTransitive : seed.1.IsTransitive) :
    seed.1 ⊆ MostowskiCollapse.range
      (textbookFiniteFragmentHull U default sentences seed) := by
  intro x hxSeed
  let domain := textbookFiniteFragmentHull U default sentences seed
  have hxDomain : x ∈ domain :=
    seed_subset_textbookFiniteFragmentHull U default sentences seed hxSeed
  have hxFixed : MostowskiCollapse.collapse domain x = x :=
    MostowskiCollapse.collapse_eq_self_of_mem_of_transitive_seed
      hseedTransitive
      (seed_subset_textbookFiniteFragmentHull U default sentences seed)
      x hxSeed
  exact MostowskiCollapse.mem_range_iff.mpr ⟨x, hxDomain, hxFixed⟩

/-- Every listed sentence is absolute between the ambient transitive set and
the transitive Mostowski collapse of the finite-fragment hull. -/
theorem satisfiesIn_textbookFiniteFragmentCollapseRange_iff_of_mem
    (U : ZFSet.{u}) (hUTransitive : U.IsTransitive)
    (default : ZFCarrier U) (sentences : List (FOFormula 0))
    (seed : ZFSubset U) {sentence : FOFormula 0}
    (hsentence : sentence ∈ sentences) :
    Model.SatisfiesIn
        (MostowskiCollapse.range
          (textbookFiniteFragmentHull U default sentences seed) :
            Set ZFSet.{u})
        sentence (fun i => Fin.elim0 i) ↔
      Model.SatisfiesIn (U : Set ZFSet.{u})
        sentence (fun i => Fin.elim0 i) := by
  calc
    Model.SatisfiesIn
        (MostowskiCollapse.range
          (textbookFiniteFragmentHull U default sentences seed) :
            Set ZFSet.{u})
        sentence (fun i => Fin.elim0 i) ↔
      Model.SatisfiesIn
        (textbookFiniteFragmentHull U default sentences seed :
          Set ZFSet.{u})
        sentence (fun i => Fin.elim0 i) :=
      MostowskiCollapse.satisfiesIn_range_sentence_iff_domain
        (textbookFiniteFragmentHull_isExtensional
          U hUTransitive default sentences seed) sentence
    _ ↔ Model.SatisfiesIn (U : Set ZFSet.{u})
        sentence (fun i => Fin.elim0 i) :=
      satisfiesIn_textbookFiniteFragmentHull_iff_of_mem
        U default sentences seed hsentence

/-- The Mostowski collapse is an isomorphism, so its transitive range has
exactly the same external `ZFSet.card` as the finite-fragment hull. -/
theorem card_textbookFiniteFragmentCollapseRange_eq_hull
    (U : ZFSet.{u}) (hUTransitive : U.IsTransitive)
    (default : ZFCarrier U) (sentences : List (FOFormula 0))
    (seed : ZFSubset U) :
    ZFSet.card
        (MostowskiCollapse.range
          (textbookFiniteFragmentHull U default sentences seed)) =
      ZFSet.card (textbookFiniteFragmentHull U default sentences seed) := by
  have hmk := Cardinal.mk_congr
    (MostowskiCollapse.equivRange
      (textbookFiniteFragmentHull_isExtensional
        U hUTransitive default sentences seed))
  rw [← Cardinal.lift_inj.{u, u + 1}]
  simpa only [ZFSet.cardinalMk_coe_sort] using hmk.symm

/-- The transitive collapse inherits the exact textbook maximum bound from
the omega Skolem closure. -/
theorem card_textbookFiniteFragmentCollapseRange_le_max
    (U : ZFSet.{u}) (hUTransitive : U.IsTransitive)
    (default : ZFCarrier U) (sentences : List (FOFormula 0))
    (seed : ZFSubset U) :
    ZFSet.card
        (MostowskiCollapse.range
          (textbookFiniteFragmentHull U default sentences seed)) ≤
      max Cardinal.aleph0 (ZFSet.card seed.1) := by
  rw [card_textbookFiniteFragmentCollapseRange_eq_hull
    U hUTransitive default sentences seed]
  exact card_textbookSkolemOmegaUnion_le_max U default
    (textbookFiniteFragmentMatrices sentences) seed

/-- Subtype-cardinality spelling of the collapse bound. -/
theorem cardinalMk_textbookFiniteFragmentCollapseRange_le_max
    (U : ZFSet.{u}) (hUTransitive : U.IsTransitive)
    (default : ZFCarrier U) (sentences : List (FOFormula 0))
    (seed : ZFSubset U) :
    Cardinal.mk (ZFCarrier
        (MostowskiCollapse.range
          (textbookFiniteFragmentHull U default sentences seed))) ≤
      max Cardinal.aleph0 (Cardinal.mk (ZFCarrier seed.1)) := by
  have hLift :
      Cardinal.lift.{u + 1, u}
          (ZFSet.card
            (MostowskiCollapse.range
              (textbookFiniteFragmentHull U default sentences seed))) ≤
        Cardinal.lift.{u + 1, u}
          (max Cardinal.aleph0 (ZFSet.card seed.1)) :=
    Cardinal.lift_monotone
      (card_textbookFiniteFragmentCollapseRange_le_max
        U hUTransitive default sentences seed)
  simpa only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_max,
    Cardinal.lift_aleph0] using hLift

/-- Structural core of Wang's Section 6.3, Theorem 3.  The witness is a
transitive set containing the transitive seed and preserving exactly the
displayed finite list of sentences.  The textbook cardinal estimate is a
separate conjunct in the cardinal refinement proved after the hull bound. -/
theorem exists_transitive_textbookFiniteFragmentReflection_core
    (U : ZFSet.{u}) (hUTransitive : U.IsTransitive)
    (default : ZFCarrier U) (sentences : List (FOFormula 0))
    (seed : ZFSubset U) (hseedTransitive : seed.1.IsTransitive) :
    ∃ z : ZFSet.{u},
      seed.1 ⊆ z ∧ z.IsTransitive ∧
        ∀ sentence : FOFormula 0, sentence ∈ sentences →
          (Model.SatisfiesIn (z : Set ZFSet.{u})
              sentence (fun i => Fin.elim0 i) ↔
            Model.SatisfiesIn (U : Set ZFSet.{u})
              sentence (fun i => Fin.elim0 i)) := by
  let domain := textbookFiniteFragmentHull U default sentences seed
  refine ⟨MostowskiCollapse.range domain, ?_,
    MostowskiCollapse.range_isTransitive domain, ?_⟩
  · exact seed_subset_textbookFiniteFragmentCollapseRange
      U default sentences seed hseedTransitive
  · intro sentence hsentence
    exact satisfiesIn_textbookFiniteFragmentCollapseRange_iff_of_mem
      U hUTransitive default sentences seed hsentence

/--
Set-sized form of Wang's Section 6.3, Theorem 3.  The ambient structure is a
transitive `ZFSet`; the finite list consists of sentences; and the seed is a
transitive subset.  The default used by every empty Skolem fiber is the least
element of the fixed metatheoretic well-order, exactly as in the textbook.

The theorem concludes, without a full-elementarity hypothesis, that there is
a transitive set containing the seed, preserving every listed sentence, and
having cardinality at most `max aleph0 (card seed)`.
-/
theorem exists_transitive_textbookFiniteFragmentReflection
    (U : ZFSet.{u}) (hUTransitive : U.IsTransitive)
    (hUNonempty : Nonempty (ZFCarrier U))
    (sentences : List (FOFormula 0))
    (seed : ZFSubset U) (hseedTransitive : seed.1.IsTransitive) :
    ∃ z : ZFSet.{u},
      seed.1 ⊆ z ∧ z.IsTransitive ∧
        (∀ sentence : FOFormula 0, sentence ∈ sentences →
          (Model.SatisfiesIn (z : Set ZFSet.{u})
              sentence (fun i => Fin.elim0 i) ↔
            Model.SatisfiesIn (U : Set ZFSet.{u})
              sentence (fun i => Fin.elim0 i))) ∧
        ZFSet.card z ≤ max Cardinal.aleph0 (ZFSet.card seed.1) := by
  let default := textbookSkolemDefault U hUNonempty
  let domain := textbookFiniteFragmentHull U default sentences seed
  refine ⟨MostowskiCollapse.range domain, ?_,
    MostowskiCollapse.range_isTransitive domain, ?_, ?_⟩
  · exact seed_subset_textbookFiniteFragmentCollapseRange
      U default sentences seed hseedTransitive
  · intro sentence hsentence
    exact satisfiesIn_textbookFiniteFragmentCollapseRange_iff_of_mem
      U hUTransitive default sentences seed hsentence
  · exact card_textbookFiniteFragmentCollapseRange_le_max
      U hUTransitive default sentences seed

end

end Constructible
