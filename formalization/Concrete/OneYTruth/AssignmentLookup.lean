import OneYTruth.ConstructibleSatisfaction

/-!
# The genuine full variable-lookup relation for reversed assignments

The relation stores (assignment code, variable index, value). Its head/tail
transport is exact: extending by `Fin.snoc` keeps every old variable index
and adds the new value at the former arity.
-/

namespace OneYTruth.AssignmentLookup

open Constructible Constructible.FiniteSequenceZF Constructible.Godel
open CodedPaths InternalNodes

universe u

abbrev Witness (U : ZFSet.{u}) := Σ n : Nat, (Fin n → ZFCarrier U) × Fin n

noncomputable def witnessCode {U : ZFSet.{u}} (w : Witness U) : ZFSet.{u} :=
  triple (assignmentCode w.2.1) (natCode w.2.2.val) (w.2.1 w.2.2).val

noncomputable def lookupSet (U : ZFSet.{u}) : ZFSet.{u} := ZFSet.range (witnessCode (U := U))

def Lookup (U : ZFSet.{u}) (a i x : ZFSet.{u}) : Prop :=
  ∃ n : Nat, ∃ v : Fin n → ZFCarrier U, ∃ j : Fin n,
    assignmentCode v = a ∧ natCode j.val = i ∧ (v j).val = x

theorem mem_lookupSet_iff (U : ZFSet.{u}) (a i x : ZFSet.{u}) :
    triple a i x ∈ lookupSet U ↔ Lookup U a i x := by
  rw [lookupSet, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨n, v, j⟩, h⟩
    obtain ⟨ha, hix⟩ := ZFSet.pair_inj.mp h
    obtain ⟨hi, hx⟩ := ZFSet.pair_inj.mp hix
    exact ⟨n, v, j, ha, hi, hx⟩
  · rintro ⟨n, v, j, ha, hi, hx⟩
    exact ⟨⟨n, v, j⟩, congrArg₂ ZFSet.pair ha (congrArg₂ ZFSet.pair hi hx)⟩

theorem lookup_assignment_iff {U : ZFSet.{u}} {n : Nat}
    (v : Fin n → ZFCarrier U) (i : Fin n) (x : ZFSet.{u}) :
    Lookup U (assignmentCode v) (natCode i.val) x ↔ (v i).val = x := by
  constructor
  · rintro ⟨m, w, j, hcode, hindex, hx⟩
    have hmn := assignmentCode_arity_eq hcode
    subst m
    have hwv := assignmentCode_injective hcode
    subst w
    have hji : j = i := Fin.ext (natCode_injective hindex)
    subst j
    exact hx
  · intro hx
    exact ⟨n, v, i, rfl, rfl, hx⟩

theorem component_pair_iff (p a b : ZFSet.{u}) :
    Component false p a ∧ Component true p b ↔ p = ZFSet.pair a b := by
  constructor
  · rintro ⟨⟨q, hp⟩, hb⟩
    have hq : b = q := component_pair.mp (hp ▸ hb)
    exact hp.trans (congrArg (ZFSet.pair a) hq.symm)
  · rintro rfl
    exact ⟨⟨b, rfl⟩, ⟨a, rfl⟩⟩

theorem payload_eq_of_paths {U : ZFSet.{u}} {n m : Nat}
    (v : Fin n → ZFCarrier U) (w : Fin m → ZFCarrier U) (a : ZFCarrier U)
    (hhead : Follows [true, false] (assignmentCode w) a.val)
    (htail : ∃ t, Follows [true, true] (assignmentCode w) t ∧
      Follows [true] (assignmentCode v) t) :
    assignmentPayload w = ZFSet.pair a.val (assignmentPayload v) := by
  apply (component_pair_iff _ _ _).mp
  constructor
  · rw [assignmentCode_eq_pair, follows_pair] at hhead
    change Follows [false] (assignmentPayload w) a.val at hhead
    simpa only [Follows, exists_eq_right] using hhead
  · simp only [assignmentCode_eq_pair] at htail
    simp only [follows_pair] at htail
    simp only [Follows, exists_eq_right] at htail
    obtain ⟨t, ht, hvt⟩ := htail
    simp only [if_true] at ht hvt
    exact hvt.symm ▸ ht

theorem lookup_transport {U : ZFSet.{u}} {parent child i x N : ZFSet.{u}}
    (hp : parent ∈ assignmentCodes U) (hc : child ∈ assignmentCodes U)
    (a : ZFCarrier U) (hscope : Follows [false] child N)
    (hhead : Follows [true, false] parent a.val)
    (htail : ∃ t, Follows [true, true] parent t ∧ Follows [true] child t)
    (hlookup : (i = N ∧ x = a.val) ∨ Lookup U child i x) : Lookup U parent i x := by
  obtain ⟨⟨n, v⟩, rfl⟩ := ZFSet.mem_range.mp hc
  obtain ⟨⟨m, w⟩, rfl⟩ := ZFSet.mem_range.mp hp
  have hparent := assignmentCode_eq_snoc_of_payload v w a (payload_eq_of_paths v w a hhead htail)
  have hN : N = natCode n := by
    rw [assignmentCode_eq_pair, follows_pair] at hscope
    exact hscope.symm
  rw [hparent]
  rcases hlookup with ⟨hi, hx⟩ | ⟨r, t, j, ht, hj, hx⟩
  · exact ⟨n + 1, Fin.snoc v a, Fin.last n, rfl, (hi.trans hN).symm, by simpa using hx.symm⟩
  · have hrn := assignmentCode_arity_eq ht
    subst r
    have htv := assignmentCode_injective ht
    subst t
    exact ⟨n + 1, Fin.snoc v a, j.castSucc, rfl, hj, by simpa using hx⟩

end OneYTruth.AssignmentLookup
