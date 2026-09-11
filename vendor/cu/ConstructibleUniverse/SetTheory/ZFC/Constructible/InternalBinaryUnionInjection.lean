/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalInfiniteCardinalAbsorption
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalProductInjections

/-!
# Internally represented injections for binary unions

The standard cardinal estimate for one Skolem step uses the fact that a
finite union of sets of size at most an infinite cardinal again has size at
most that cardinal.  This file proves the binary case with an actual
Kuratowski graph in `L`.

The two summands are tagged by the internal natural numbers zero and one.
The resulting graph maps the union into `kappa x kappa`; a supplied internal
square-absorption graph then gives the desired injection into `kappa`.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-- The disjointly tagged relation used to inject a binary union.  Elements
of the left set use the left graph and tag zero.  Elements belonging only to
the right set use the right graph and tag one. -/
def TaggedUnionInjectionRel {A : Type u} (E : A -> A -> Prop)
    (left right first second zero one input output : A) : Prop :=
  (E input left /\
      exists image : A,
        GraphValue E first input image /\
          IsKuratowskiPairOf E output zero image) \/
    (Not (E input left) /\ E input right /\
      exists image : A,
        GraphValue E second input image /\
          IsKuratowskiPairOf E output one image)

/-- Layout `(left,right,first,second,zero,one,input,output)`. -/
def taggedUnionInjectionFormula : FOFormula 8 :=
  .disj
    (.conj
      (.mem (6 : Fin 8) (0 : Fin 8))
      (.ex <| .conj
        (graphValueAt
          (2 : Fin 8).castSucc (6 : Fin 8).castSucc (Fin.last 8))
        (kuratowskiPairAt
          (7 : Fin 8).castSucc (4 : Fin 8).castSucc (Fin.last 8))))
    (.conj
      (.neg (.mem (6 : Fin 8) (0 : Fin 8)))
      (.conj
        (.mem (6 : Fin 8) (1 : Fin 8))
        (.ex <| .conj
          (graphValueAt
            (3 : Fin 8).castSucc (6 : Fin 8).castSucc (Fin.last 8))
          (kuratowskiPairAt
            (7 : Fin 8).castSucc (5 : Fin 8).castSucc (Fin.last 8)))))

private theorem taggedUnionInjection_assignment
    (left right first second zero one input output image : LCarrier.{u}) :
    snoc ![left, right, first, second, zero, one, input, output] image =
      ![left, right, first, second, zero, one, input, output, image] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_taggedUnionInjectionFormula
    (left right first second zero one input output : LCarrier.{u}) :
    FOFormula.Satisfies LMem taggedUnionInjectionFormula
        ![left, right, first, second, zero, one, input, output] <->
      TaggedUnionInjectionRel LMem
        left right first second zero one input output := by
  simp only [taggedUnionInjectionFormula, FOFormula.satisfies_disj,
    FOFormula.Satisfies, satisfies_graphValueAt,
    satisfies_kuratowskiPairAt, TaggedUnionInjectionRel]
  apply or_congr
  · apply and_congr Iff.rfl
    apply exists_congr
    intro image
    rw [taggedUnionInjection_assignment]
    rfl
  · apply and_congr Iff.rfl
    apply and_congr Iff.rfl
    apply exists_congr
    intro image
    rw [taggedUnionInjection_assignment]
    rfl

private theorem taggedUnionInjection_relation_assignment
    (left right first second zero one input output : LCarrier.{u}) :
    snoc (snoc ![left, right, first, second, zero, one] input) output =
      ![left, right, first, second, zero, one, input, output] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_taggedUnionInjectionRelation
    (left right first second zero one input output : LCarrier.{u}) :
    FOFormula.Satisfies LMem taggedUnionInjectionFormula
        (snoc (snoc ![left, right, first, second, zero, one] input) output) <->
      TaggedUnionInjectionRel LMem
        left right first second zero one input output := by
  rw [taggedUnionInjection_relation_assignment,
    satisfies_taggedUnionInjectionFormula]

/-- The tagged relation is represented by a genuine internal injection into
`kappa x kappa`. -/
theorem injects_binaryUnion_into_square_lCarrier
    {left right kappa : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hleft : Injects LMem left kappa)
    (hright : Injects LMem right kappa) :
    Injects LMem (unionLCarrier left right) (prodLCarrier kappa kappa) := by
  rcases hleft with ⟨first, hfirst⟩
  rcases hright with ⟨second, hsecond⟩
  let zero : LCarrier.{u} := natLCarrier 0
  let one : LCarrier.{u} := natLCarrier 1
  let domain := unionLCarrier left right
  let codomain := prodLCarrier kappa kappa
  let support := unionLCarrier domain codomain
  have hzeroOmega : zero.1 ∈ omegaLCarrier.1 := by
    change (FiniteSequenceZF.natCode 0 : ZFSet.{u}) ∈
      Ordinal.omega0.toZFSet
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr <|
      Exists.intro 0 rfl
  have honeOmega : one.1 ∈ omegaLCarrier.1 := by
    change (FiniteSequenceZF.natCode 1 : ZFSet.{u}) ∈
      Ordinal.omega0.toZFSet
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr <|
      Exists.intro 1 rfl
  have hzeroKappa : zero.1 ∈ kappa.1 := homega zero hzeroOmega
  have honeKappa : one.1 ∈ kappa.1 := homega one honeOmega
  have hzeroOne : zero ≠ one := by
    intro h
    have hcode :
        (FiniteSequenceZF.natCode 0 : ZFSet.{u}) =
          FiniteSequenceZF.natCode 1 := congrArg Subtype.val h
    exact Nat.zero_ne_one (FiniteSequenceZF.natCode_injective hcode)
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      taggedUnionInjectionFormula ![left, right, first, second, zero, one]
      support with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : forall input output : LCarrier.{u},
      GraphValue LMem graph input output <->
        TaggedUnionInjectionRel LMem
          left right first second zero one input output := by
    intro input output
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨_hinputSupport, _houtputSupport, hformula⟩
      exact (satisfies_taggedUnionInjectionRelation
        left right first second zero one input output).mp hformula
    · intro hrel
      have hinputDomain : input.1 ∈ domain.1 := by
        rcases hrel with hrel | hrel
        · exact (mem_unionLCarrier_iff left right input).mpr <| Or.inl hrel.1
        · exact (mem_unionLCarrier_iff left right input).mpr <| Or.inr hrel.2.1
      have houtputCodomain : output.1 ∈ codomain.1 := by
        rcases hrel with hrel | hrel
        · rcases hrel.2 with ⟨image, himage, hpair⟩
          have himageKappa := hfirst.1.graphValue_mem_lCarrier himage |>.2
          have houtput := (isKuratowskiPairOf_lCarrier_iff
            output zero image).mp hpair
          change output.1 ∈ ZFSet.prod kappa.1 kappa.1
          rw [houtput, ZFSet.pair_mem_prod]
          exact And.intro hzeroKappa himageKappa
        · rcases hrel.2.2 with ⟨image, himage, hpair⟩
          have himageKappa := hsecond.1.graphValue_mem_lCarrier himage |>.2
          have houtput := (isKuratowskiPairOf_lCarrier_iff
            output one image).mp hpair
          change output.1 ∈ ZFSet.prod kappa.1 kappa.1
          rw [houtput, ZFSet.pair_mem_prod]
          exact And.intro honeKappa himageKappa
      refine And.intro
        ((mem_unionLCarrier_iff domain codomain input).mpr <| Or.inl hinputDomain) <|
        And.intro
          ((mem_unionLCarrier_iff domain codomain output).mpr <| Or.inr houtputCodomain) ?_
      exact (satisfies_taggedUnionInjectionRelation
        left right first second zero one input output).mpr hrel
  have hbetween : IsGraphBetween LMem graph domain codomain := by
    intro pair hpair
    rcases hsupport pair hpair with
      ⟨input, output, _hinputSupport, _houtputSupport, hpairEq, hformula⟩
    have hrel := (satisfies_taggedUnionInjectionRelation
      left right first second zero one input output).mp hformula
    have hmem : input.1 ∈ domain.1 ∧ output.1 ∈ codomain.1 := by
      rcases hrel with hrel | hrel
      · have hx := hfirst.1.graphValue_mem_lCarrier hrel.2.choose_spec.1
        exact And.intro
          ((mem_unionLCarrier_iff left right input).mpr <| Or.inl hrel.1)
          (by
            have hp := (isKuratowskiPairOf_lCarrier_iff
              output zero hrel.2.choose).mp hrel.2.choose_spec.2
            change output.1 ∈ ZFSet.prod kappa.1 kappa.1
            rw [hp, ZFSet.pair_mem_prod]
            exact And.intro hzeroKappa hx.2)
      · have hx := hsecond.1.graphValue_mem_lCarrier hrel.2.2.choose_spec.1
        exact And.intro
          ((mem_unionLCarrier_iff left right input).mpr <| Or.inr hrel.2.1)
          (by
            have hp := (isKuratowskiPairOf_lCarrier_iff
              output one hrel.2.2.choose).mp hrel.2.2.choose_spec.2
            change output.1 ∈ ZFSet.prod kappa.1 kappa.1
            rw [hp, ZFSet.pair_mem_prod]
            exact And.intro honeKappa hx.2)
    exact Exists.intro input <| And.intro hmem.1 <|
      Exists.intro output <| And.intro hmem.2 <|
        (isKuratowskiPairOf_lCarrier_iff pair input output).mpr hpairEq
  refine Exists.intro graph <| And.intro hbetween <| And.intro ?_ ?_
  · intro input hinput
    rcases (mem_unionLCarrier_iff left right input).mp hinput with
      hinputLeft | hinputRight
    · rcases hfirst.2.1 input hinputLeft with
        ⟨image, himageKappa, himage, himageUnique⟩
      let output := orderedPairLCarrier zero image
      have houtput : output.1 ∈ codomain.1 := by
        change ZFSet.pair zero.1 image.1 ∈ ZFSet.prod kappa.1 kappa.1
        rw [ZFSet.pair_mem_prod]
        exact And.intro hzeroKappa himageKappa
      refine Exists.intro output <| And.intro houtput <|
        And.intro ((hvalue input output).mpr <| Or.inl <|
          And.intro hinputLeft <| Exists.intro image <|
            And.intro himage <|
              (isKuratowskiPairOf_lCarrier_iff output zero image).mpr rfl) ?_
      intro other _hother hinputOther
      rcases (hvalue input other).mp hinputOther with hotherLeft | hotherRight
      · rcases hotherLeft.2 with ⟨otherImage, hotherImage, hotherPair⟩
        have hotherImageKappa :=
          hfirst.1.graphValue_mem_lCarrier hotherImage |>.2
        have himageEq := himageUnique otherImage hotherImageKappa hotherImage
        subst otherImage
        apply Subtype.ext
        exact ((isKuratowskiPairOf_lCarrier_iff other zero image).mp
          hotherPair).trans rfl.symm
      · exact (hotherRight.1 hinputLeft).elim
    · by_cases hinputLeft : input.1 ∈ left.1
      · rcases hfirst.2.1 input hinputLeft with
          ⟨image, himageKappa, himage, himageUnique⟩
        let output := orderedPairLCarrier zero image
        have houtput : output.1 ∈ codomain.1 := by
          change ZFSet.pair zero.1 image.1 ∈ ZFSet.prod kappa.1 kappa.1
          rw [ZFSet.pair_mem_prod]
          exact And.intro hzeroKappa himageKappa
        refine Exists.intro output <| And.intro houtput <|
          And.intro ((hvalue input output).mpr <| Or.inl <|
            And.intro hinputLeft <| Exists.intro image <|
              And.intro himage <|
                (isKuratowskiPairOf_lCarrier_iff output zero image).mpr rfl) ?_
        intro other _hother hinputOther
        rcases (hvalue input other).mp hinputOther with hotherLeft | hotherRight
        · rcases hotherLeft.2 with ⟨otherImage, hotherImage, hotherPair⟩
          have hotherImageKappa :=
            hfirst.1.graphValue_mem_lCarrier hotherImage |>.2
          have himageEq := himageUnique otherImage hotherImageKappa hotherImage
          subst otherImage
          exact Subtype.ext <|
            ((isKuratowskiPairOf_lCarrier_iff other zero image).mp
              hotherPair).trans rfl.symm
        · exact (hotherRight.1 hinputLeft).elim
      · rcases hsecond.2.1 input hinputRight with
          ⟨image, himageKappa, himage, himageUnique⟩
        let output := orderedPairLCarrier one image
        have houtput : output.1 ∈ codomain.1 := by
          change ZFSet.pair one.1 image.1 ∈ ZFSet.prod kappa.1 kappa.1
          rw [ZFSet.pair_mem_prod]
          exact And.intro honeKappa himageKappa
        refine Exists.intro output <| And.intro houtput <|
          And.intro ((hvalue input output).mpr <| Or.inr <|
            And.intro hinputLeft <| And.intro hinputRight <|
              Exists.intro image <| And.intro himage <|
                (isKuratowskiPairOf_lCarrier_iff output one image).mpr rfl) ?_
        intro other _hother hinputOther
        rcases (hvalue input other).mp hinputOther with hotherLeft | hotherRight
        · exact (hinputLeft hotherLeft.1).elim
        · rcases hotherRight.2.2 with ⟨otherImage, hotherImage, hotherPair⟩
          have hotherImageKappa :=
            hsecond.1.graphValue_mem_lCarrier hotherImage |>.2
          have himageEq := himageUnique otherImage hotherImageKappa hotherImage
          subst otherImage
          exact Subtype.ext <|
            ((isKuratowskiPairOf_lCarrier_iff other one image).mp
              hotherPair).trans rfl.symm
  · intro output _houtput input hinput hinputOutput other hother hotherOutput
    rcases (hvalue input output).mp hinputOutput with hinputLeft | hinputRight <;>
      rcases (hvalue other output).mp hotherOutput with hotherLeft | hotherRight
    · rcases hinputLeft.2 with ⟨inputImage, hinputImage, hinputPair⟩
      rcases hotherLeft.2 with ⟨otherImage, hotherImage, hotherPair⟩
      have hpairs := ZFSet.pair_inj.mp <|
        ((isKuratowskiPairOf_lCarrier_iff output zero inputImage).mp
          hinputPair).symm.trans
        ((isKuratowskiPairOf_lCarrier_iff output zero otherImage).mp hotherPair)
      have himageEq : inputImage = otherImage := Subtype.ext hpairs.2
      subst otherImage
      exact hfirst.2.2 inputImage
        (hfirst.1.graphValue_mem_lCarrier hinputImage |>.2)
        input hinputLeft.1 hinputImage other hotherLeft.1 hotherImage
    · rcases hinputLeft.2 with ⟨inputImage, _hinputImage, hinputPair⟩
      rcases hotherRight.2.2 with ⟨otherImage, _hotherImage, hotherPair⟩
      have hpairs := ZFSet.pair_inj.mp <|
        ((isKuratowskiPairOf_lCarrier_iff output zero inputImage).mp
          hinputPair).symm.trans
        ((isKuratowskiPairOf_lCarrier_iff output one otherImage).mp hotherPair)
      exact (hzeroOne <| Subtype.ext hpairs.1).elim
    · rcases hinputRight.2.2 with ⟨inputImage, _hinputImage, hinputPair⟩
      rcases hotherLeft.2 with ⟨otherImage, _hotherImage, hotherPair⟩
      have hpairs := ZFSet.pair_inj.mp <|
        ((isKuratowskiPairOf_lCarrier_iff output one inputImage).mp
          hinputPair).symm.trans
        ((isKuratowskiPairOf_lCarrier_iff output zero otherImage).mp hotherPair)
      exact (hzeroOne <| (Subtype.ext hpairs.1).symm).elim
    · rcases hinputRight.2.2 with ⟨inputImage, hinputImage, hinputPair⟩
      rcases hotherRight.2.2 with ⟨otherImage, hotherImage, hotherPair⟩
      have hpairs := ZFSet.pair_inj.mp <|
        ((isKuratowskiPairOf_lCarrier_iff output one inputImage).mp
          hinputPair).symm.trans
        ((isKuratowskiPairOf_lCarrier_iff output one otherImage).mp hotherPair)
      have himageEq : inputImage = otherImage := Subtype.ext hpairs.2
      subst otherImage
      exact hsecond.2.2 inputImage
        (hsecond.1.graphValue_mem_lCarrier hinputImage |>.2)
        input hinputRight.2.1 hinputImage other hotherRight.2.1 hotherImage

/-- Binary unions preserve an internal infinite-cardinal bound. -/
theorem injects_binaryUnion_lCarrier
    {left right kappa : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hsquare : Injects LMem (prodLCarrier kappa kappa) kappa)
    (hleft : Injects LMem left kappa)
    (hright : Injects LMem right kappa) :
    Injects LMem (unionLCarrier left right) kappa :=
  (injects_binaryUnion_into_square_lCarrier homega hleft hright).trans_lCarrier
    hsquare

end

end Constructible.ContinuumFormula
