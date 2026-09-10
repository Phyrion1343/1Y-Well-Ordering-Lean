import OneYTruth.DeltaSyntaxGrammar

/-! # The bounded grammar produces precisely scoped Delta-zero syntax -/

namespace OneYTruth.DeltaSyntaxGrammar

open FirstOrder FirstOrder.Language Constructible Constructible.FiniteSequenceZF FormulaCode
open Constructible.IndexedSequenceZF (mem_natCode_iff_exists_lt)

universe u v

def Scoped {k : Nat} {I : Type v} (indexCode : I → ZFSet.{u}) (n : Nat) (f : ZFSet.{u}) : Prop :=
  ∃ φ : (language k I).BoundedFormula Empty n, IsDeltaZero φ ∧ formulaCode indexCode φ = f

abbrev DeltaPacked (k : Nat) (I : Type v) := {φ : Packed k I // IsDeltaZero φ.2}

noncomputable def deltaCodes {k : Nat} {I : Type v} [Small.{u} I]
    (indexCode : I → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun φ : DeltaPacked k I => packedCode indexCode φ.val)

theorem scoped_of_packed {k : Nat} {I : Type v} {indexCode : I → ZFSet.{u}}
    {n : Nat} {f : ZFSet.{u}}
    (h : ∃ p : DeltaPacked k I, packedCode indexCode p.val = ZFSet.pair (natCode n) f) :
    Scoped (k := k) indexCode n f := by
  obtain ⟨⟨⟨m, φ⟩, hφ⟩, h⟩ := h
  obtain ⟨hn, hf⟩ := ZFSet.pair_inj.mp h
  have hmn : m = n := natCode_injective hn
  subst m
  exact ⟨φ, hφ, hf⟩

theorem rawRule_sound {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} {B A S f : ZFSet.{u}}
    (hA : A = ZFSet.range indexCode)
    (hS : ∀ n g, ZFSet.pair (natCode n) g ∈ S → Scoped (k := k) indexCode n g)
    (n : Nat)
    (hf : RawRule B A Ordinal.omega0.toZFSet (natCode k) S (natCode n) f) :
    Scoped (k := k) indexCode n f := by
  rcases hf with hf | hf | hf | hf | hf | hf | hf
  · exact ⟨.falsum, .falsum, hf.symm⟩
  · obtain ⟨i, hi, j, hj, hf⟩ := hf
    obtain ⟨a, ha, rfl⟩ := (mem_natCode_iff_exists_lt i n).mp hi
    obtain ⟨b, hb, rfl⟩ := (mem_natCode_iff_exists_lt j n).mp hj
    exact ⟨.equal (.var (.inr ⟨a, ha⟩)) (.var (.inr ⟨b, hb⟩)), .equal _ _, hf.symm⟩
  · obtain ⟨i, hi, j, hj, hf⟩ := hf
    obtain ⟨a, ha, rfl⟩ := (mem_natCode_iff_exists_lt i n).mp hi
    obtain ⟨b, hb, rfl⟩ := (mem_natCode_iff_exists_lt j n).mp hj
    exact ⟨.rel .mem ![.var (.inr ⟨a, ha⟩), .var (.inr ⟨b, hb⟩)], .rel _ _, hf.symm⟩
  · obtain ⟨j, hj, ξ, hξ, e, he, a, ha, hf⟩ := hf
    obtain ⟨jN, hjN, rfl⟩ := (mem_natCode_iff_exists_lt j k).mp hj
    obtain ⟨ξN, hξN, rfl⟩ := (mem_natCode_iff_exists_lt ξ n).mp hξ
    obtain ⟨eN, heN, rfl⟩ := (mem_natCode_iff_exists_lt e n).mp he
    obtain ⟨aN, haN, rfl⟩ := (mem_natCode_iff_exists_lt a n).mp ha
    exact ⟨.rel (.diagonal ⟨jN, hjN⟩)
      ![.var (.inr ⟨ξN, hξN⟩), .var (.inr ⟨eN, heN⟩), .var (.inr ⟨aN, haN⟩)], .rel _ _, hf.symm⟩
  · obtain ⟨ξ, hξ, e, he, a, ha, hf⟩ := hf
    rw [hA] at hξ
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hξ
    obtain ⟨eN, heN, rfl⟩ := (mem_natCode_iff_exists_lt e n).mp he
    obtain ⟨aN, haN, rfl⟩ := (mem_natCode_iff_exists_lt a n).mp ha
    exact ⟨.rel (.named i) ![.var (.inr ⟨eN, heN⟩), .var (.inr ⟨aN, haN⟩)], .rel _ _, hf.symm⟩
  · obtain ⟨g, _, h, _, hf, hg, hh⟩ := hf
    obtain ⟨φ, hδφ, hφ⟩ := hS n g hg
    obtain ⟨ψ, hδψ, hψ⟩ := hS n h hh
    refine ⟨.imp φ ψ, .imp hδφ hδψ, ?_⟩
    change sequenceCode [natCode 5, formulaCode indexCode φ, formulaCode indexCode ψ] = f
    rw [hφ, hψ]
    exact hf.symm
  · obtain ⟨i, hi, g, _, j, _, a, _, b, _, hj, ha, hb, hf, hg⟩ := hf
    obtain ⟨iN, hiN, rfl⟩ := (mem_natCode_iff_exists_lt i n).mp hi
    have hj' : j = natCode (n+1) := hj.trans (natCode_succ_eq_insert n).symm
    rw [hj'] at hg
    obtain ⟨φ, hδφ, hφ⟩ := hS (n+1) g hg
    refine ⟨OneYTruth.boundedAll (.var (.inr ⟨iN, hiN⟩)) φ, .boundedAll _ hδφ, ?_⟩
    rw [formulaCode_boundedAll, hφ]
    change sequenceCode [natCode 6, sequenceCode [natCode 5,
      sequenceCode [natCode 2, natCode n, natCode iN], g] ] = f
    rw [← ha, ← hb]
    exact hf.symm

end OneYTruth.DeltaSyntaxGrammar

#print axioms OneYTruth.DeltaSyntaxGrammar.rawRule_sound
