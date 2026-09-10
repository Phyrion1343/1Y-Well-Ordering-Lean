import OneYTruth.ConstructibleSatisfaction

/-!
# Genuine set graphs for the atomic predicate interpretations

These sets encode the actual named and diagonal relations. Their
constructibility is a separate condition until supplied by a preceding
canonical tower graph.
-/

namespace OneYTruth.AtomicRelationGraphs

open Constructible Constructible.FiniteSequenceZF Constructible.Godel
open Constructible.Delta0Formula FiniteCodeFormula

universe u v

def quad (a b c d : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair a (triple b c d)

abbrev NamedWitness {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (M : Interpretation k I (ZFCarrier U)) :=
  {z : I × ZFCarrier U × ZFCarrier U // M.named z.1 z.2.1 z.2.2}

noncomputable def namedGraph {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (M : Interpretation k I (ZFCarrier U)) : ZFSet.{u} :=
  ZFSet.range (fun z : NamedWitness M => triple (indexCode z.val.1) z.val.2.1.val z.val.2.2.val)

abbrev DiagonalWitness {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (M : Interpretation k I (ZFCarrier U)) :=
  {z : Fin k × ZFCarrier U × ZFCarrier U × ZFCarrier U // M.diagonal z.1 z.2.1 z.2.2.1 z.2.2.2}

noncomputable def diagonalGraph {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (M : Interpretation k I (ZFCarrier U)) : ZFSet.{u} :=
  ZFSet.range (fun z : DiagonalWitness M =>
    quad (natCode z.val.1.val) z.val.2.1.val z.val.2.2.1.val z.val.2.2.2.val)

theorem mem_namedGraph_iff {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) (i : I) (x y : ZFCarrier U) :
    triple (indexCode i) x.val y.val ∈ namedGraph indexCode M ↔ M.named i x y := by
  constructor
  · intro h
    obtain ⟨⟨⟨j, a, b⟩, hj⟩, heq⟩ := ZFSet.mem_range.mp h
    obtain ⟨hji, hab⟩ := ZFSet.pair_inj.mp heq
    obtain ⟨ha, hb⟩ := ZFSet.pair_inj.mp hab
    have hj' : j = i := hi hji
    have ha' : a = x := Subtype.ext ha
    have hb' : b = y := Subtype.ext hb
    subst j a b
    exact hj
  · intro h
    exact ZFSet.mem_range_self (f := fun z : NamedWitness M =>
      triple (indexCode z.val.1) z.val.2.1.val z.val.2.2.val) ⟨(i, x, y), h⟩

theorem mem_diagonalGraph_iff {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (M : Interpretation k I (ZFCarrier U)) (i : Fin k) (x y z : ZFCarrier U) :
    quad (natCode i.val) x.val y.val z.val ∈ diagonalGraph M ↔ M.diagonal i x y z := by
  constructor
  · intro h
    obtain ⟨⟨⟨j, a, b, c⟩, hj⟩, heq⟩ := ZFSet.mem_range.mp h
    obtain ⟨hji, habc⟩ := ZFSet.pair_inj.mp heq
    obtain ⟨ha, hbc⟩ := ZFSet.pair_inj.mp habc
    obtain ⟨hb, hc⟩ := ZFSet.pair_inj.mp hbc
    have hj' : j = i := Fin.ext (natCode_injective hji)
    have ha' : a = x := Subtype.ext ha
    have hb' : b = y := Subtype.ext hb
    have hc' : c = z := Subtype.ext hc
    subst j a b c
    exact hj
  · intro h
    exact ZFSet.mem_range_self (f := fun z : DiagonalWitness M =>
      quad (natCode z.val.1.val) z.val.2.1.val z.val.2.2.1.val z.val.2.2.2.val) ⟨(i, x, y, z), h⟩

def quadMemAt {n : Nat} (r a b c d : Fin n) : Delta0Formula n :=
  .boundedEx r (chainEqAt 3 ![a.castSucc, b.castSucc, c.castSucc] (Fin.last n) d.castSucc)

theorem satisfies_quadMemAt {n : Nat} (r a b c d : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (quadMemAt r a b c d) s ↔ quad (s a) (s b) (s c) (s d) ∈ s r := by
  simp only [quadMemAt, Satisfies, satisfies_chainEqAt, snoc_last, snoc_castSucc]
  simp [chainCode, List.ofFn_succ, quad, triple, ZFMem]

end OneYTruth.AtomicRelationGraphs
