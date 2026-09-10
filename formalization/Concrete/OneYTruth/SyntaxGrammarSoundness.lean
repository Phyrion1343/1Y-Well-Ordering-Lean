import OneYTruth.SyntaxGrammar

/-! Every result of the literal grammar is an actual intrinsically scoped formula. -/

namespace OneYTruth.SyntaxGrammar

open FirstOrder FirstOrder.Language Constructible Constructible.FiniteSequenceZF
open Constructible.IndexedSequenceZF (mem_natCode_iff_exists_lt)
open FormulaCode

universe u v

def Scoped {k : Nat} {I : Type v} (indexCode : I → ZFSet.{u}) (n : Nat) (f : ZFSet.{u}) : Prop :=
  ∃ φ : (language k I).BoundedFormula Empty n, formulaCode indexCode φ = f

theorem scoped_of_packed {k : Nat} {I : Type v} {indexCode : I → ZFSet.{u}}
    {n : Nat} {f : ZFSet.{u}}
    (h : ∃ p : Packed k I, packedCode indexCode p = ZFSet.pair (natCode n) f) :
    Scoped (k := k) indexCode n f := by
  obtain ⟨⟨m, φ⟩, h⟩ := h
  obtain ⟨hn, hf⟩ := ZFSet.pair_inj.mp h
  have hmn : m = n := natCode_injective hn
  subst m
  exact ⟨φ, hf⟩

theorem rawRule_sound {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} {B A S f : ZFSet.{u}}
    (hA : A = ZFSet.range indexCode)
    (hS : ∀ n g, ZFSet.pair (natCode n) g ∈ S → Scoped (k := k) indexCode n g)
    (n : Nat)
    (hf : RawRule B A Ordinal.omega0.toZFSet (natCode k) S (natCode n) f) :
    Scoped (k := k) indexCode n f := by
  rcases hf with hf | hf | hf | hf | hf | hf | hf
  · exact ⟨.falsum, hf.symm⟩
  · obtain ⟨i, hi, j, hj, hf⟩ := hf
    obtain ⟨a, ha, rfl⟩ := (mem_natCode_iff_exists_lt i n).mp hi
    obtain ⟨b, hb, rfl⟩ := (mem_natCode_iff_exists_lt j n).mp hj
    exact ⟨.equal (.var (.inr ⟨a, ha⟩)) (.var (.inr ⟨b, hb⟩)), hf.symm⟩
  · obtain ⟨i, hi, j, hj, hf⟩ := hf
    obtain ⟨a, ha, rfl⟩ := (mem_natCode_iff_exists_lt i n).mp hi
    obtain ⟨b, hb, rfl⟩ := (mem_natCode_iff_exists_lt j n).mp hj
    exact ⟨.rel .mem ![.var (.inr ⟨a, ha⟩), .var (.inr ⟨b, hb⟩)], hf.symm⟩
  · obtain ⟨j, hj, ξ, hξ, e, he, a, ha, hf⟩ := hf
    obtain ⟨jN, hjN, rfl⟩ := (mem_natCode_iff_exists_lt j k).mp hj
    obtain ⟨ξN, hξN, rfl⟩ := (mem_natCode_iff_exists_lt ξ n).mp hξ
    obtain ⟨eN, heN, rfl⟩ := (mem_natCode_iff_exists_lt e n).mp he
    obtain ⟨aN, haN, rfl⟩ := (mem_natCode_iff_exists_lt a n).mp ha
    exact ⟨.rel (.diagonal ⟨jN, hjN⟩)
      ![.var (.inr ⟨ξN, hξN⟩), .var (.inr ⟨eN, heN⟩), .var (.inr ⟨aN, haN⟩)], hf.symm⟩
  · obtain ⟨ξ, hξ, e, he, a, ha, hf⟩ := hf
    rw [hA] at hξ
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hξ
    obtain ⟨eN, heN, rfl⟩ := (mem_natCode_iff_exists_lt e n).mp he
    obtain ⟨aN, haN, rfl⟩ := (mem_natCode_iff_exists_lt a n).mp ha
    exact ⟨.rel (.named i) ![.var (.inr ⟨eN, heN⟩), .var (.inr ⟨aN, haN⟩)], hf.symm⟩
  · obtain ⟨g, _, h, _, hf, hg, hh⟩ := hf
    obtain ⟨φ, hφ⟩ := hS n g hg
    obtain ⟨ψ, hψ⟩ := hS n h hh
    refine ⟨.imp φ ψ, ?_⟩
    change sequenceCode [natCode 5, formulaCode indexCode φ, formulaCode indexCode ψ] = f
    rw [hφ, hψ]
    exact hf.symm
  · obtain ⟨g, _, j, _, hj, hf, hg⟩ := hf
    have hj' : j = natCode (n + 1) := hj.trans (natCode_succ_eq_insert n).symm
    rw [hj'] at hg
    obtain ⟨φ, hφ⟩ := hS (n + 1) g hg
    refine ⟨.all φ, ?_⟩
    change sequenceCode [natCode 6, formulaCode indexCode φ] = f
    rw [hφ]
    exact hf.symm

end OneYTruth.SyntaxGrammar
