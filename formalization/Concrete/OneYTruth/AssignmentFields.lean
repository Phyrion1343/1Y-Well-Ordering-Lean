import OneYTruth.SatisfactionSet

/-! Fixed code fields of reversed finite assignments. -/

namespace OneYTruth

open Constructible Constructible.FiniteSequenceZF

universe u

noncomputable def assignmentPayload {U : ZFSet.{u}} {n : Nat}
    (v : Fin n → ZFCarrier U) : ZFSet.{u} :=
  listCode (List.ofFn (fun i => (v i).val)).reverse

theorem assignmentCode_eq_pair {U : ZFSet.{u}} {n : Nat} (v : Fin n → ZFCarrier U) :
    assignmentCode v = ZFSet.pair (natCode n) (assignmentPayload v) := by
  simp [assignmentCode, sequenceCode, assignmentPayload]

theorem assignmentCode_arity_eq {U : ZFSet.{u}} {n m : Nat}
    {v : Fin n → ZFCarrier U} {w : Fin m → ZFCarrier U}
    (h : assignmentCode v = assignmentCode w) : n = m := by
  have ha := (ZFSet.pair_inj.mp h).1
  simpa only [List.length_reverse, List.length_ofFn, natCode_inj] using ha

theorem assignmentCode_snoc {U : ZFSet.{u}} {n : Nat} (v : Fin n → ZFCarrier U)
    (a : ZFCarrier U) :
    assignmentCode (Fin.snoc v a) = ZFSet.pair (natCode (n + 1))
      (ZFSet.pair a.val (listCode (List.ofFn (fun i => (v i).val)).reverse)) := by
  have hs : (List.ofFn (fun i => ((Fin.snoc v a : Fin (n + 1) → ZFCarrier U) i).val)).reverse =
      a.val :: (List.ofFn (fun i => (v i).val)).reverse := by
    rw [List.ofFn_succ_last]
    simp only [Fin.snoc_last, Fin.snoc_castSucc, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
  rw [assignmentCode, hs, sequenceCode]
  simp only [List.length_cons, List.length_reverse, List.length_ofFn, listCode_cons]

theorem assignmentCode_eq_snoc_of_payload {U : ZFSet.{u}} {n m : Nat}
    (v : Fin n → ZFCarrier U) (w : Fin m → ZFCarrier U) (a : ZFCarrier U)
    (h : assignmentPayload w = ZFSet.pair a.val (assignmentPayload v)) :
    assignmentCode w = assignmentCode (Fin.snoc v a) := by
  have hl : (List.ofFn (fun i => (w i).val)).reverse =
      a.val :: (List.ofFn (fun i => (v i).val)).reverse := listCode_injective h
  have hm : m = n + 1 := by
    have hlen := congrArg List.length hl
    simpa only [List.length_reverse, List.length_ofFn, List.length_cons] using hlen
  rw [assignmentCode_eq_pair, assignmentCode_snoc]
  exact congrArg₂ ZFSet.pair (congrArg natCode hm) h

theorem assignmentPayload_snoc {U : ZFSet.{u}} {n : Nat} (v : Fin n → ZFCarrier U)
    (a : ZFCarrier U) : assignmentPayload (Fin.snoc v a) =
      ZFSet.pair a.val (assignmentPayload v) := by
  have h := assignmentCode_snoc v a
  rw [assignmentCode_eq_pair] at h
  exact (ZFSet.pair_inj.mp h).2

end OneYTruth
