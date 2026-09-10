import OneYTruth.ConstructibleAssignmentLookup
import OneYTruth.AtomicRelationGraphs

/-! A bounded atomic argument query with genuine variable-index lookup. -/

namespace OneYTruth.AtomicArgumentLookup

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF Constructible.Godel
open CodedPaths BoundedEvaluation AssignmentLookup InternalNodes
open Constructible.IndexedSequenceZF (mem_omega_iff_exists_natCode)

universe u

def argumentPath (field : Nat) : List Bool :=
  [false, true, true] ++ List.replicate field true ++ [false]

def Argument (path : List Bool) (lookup assignments omega node value : ZFSet.{u}) : Prop :=
  ∃ a ∈ assignments, ∃ i ∈ omega,
    Follows [true] node a ∧ Follows path node i ∧ triple a i value ∈ lookup

def argumentAt {n : Nat} (path : List Bool) (lookup assignments omega node value : Fin n) :
    Delta0Formula n :=
  .boundedEx assignments (.boundedEx omega.castSucc
    (.conj (pathEqAt [true] node.castSucc.castSucc (Fin.last n).castSucc)
      (.conj (pathEqAt path node.castSucc.castSucc (Fin.last (n + 1)))
        (tripleMemAt lookup.castSucc.castSucc (Fin.last n).castSucc
          (Fin.last (n + 1)) value.castSucc.castSucc))))

theorem satisfies_argumentAt {n : Nat} (path : List Bool)
    (lookup assignments omega node value : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (argumentAt path lookup assignments omega node value) s ↔
      Argument path (s lookup) (s assignments) (s omega) (s node) (s value) := by
  simp only [argumentAt, Satisfies, satisfies_pathEqAt, satisfies_tripleMemAt,
    snoc_last, snoc_castSucc, Argument, ZFMem]

theorem follows_listCode_get (xs : List ZFSet.{u}) (j : Fin xs.length) (x : ZFSet.{u}) :
    Follows (List.replicate j.val true ++ [false]) (listCode xs) x ↔ x = xs.get j := by
  induction xs with
  | nil => exact Fin.elim0 j
  | cons a xs ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [listCode, follows_pair, Follows, eq_comm]
    · simpa [List.replicate_succ, listCode_cons, follows_pair] using ih j

noncomputable def codedNode {U : ZFSet.{u}} {n : Nat}
    (fields : List ZFSet.{u}) (v : Fin n → ZFCarrier U) : ZFSet.{u} :=
  ZFSet.pair (ZFSet.pair (natCode n) (sequenceCode fields)) (assignmentCode v)

theorem follows_codedNode_field {U : ZFSet.{u}} {n : Nat} (fields : List ZFSet.{u})
    (v : Fin n → ZFCarrier U) (j : Fin fields.length) (x : ZFSet.{u}) :
    Follows (argumentPath j.val) (codedNode fields v) x ↔ x = fields.get j := by
  unfold argumentPath codedNode sequenceCode
  simp only [List.cons_append, List.nil_append]
  rw [follows_pair, if_neg Bool.false_ne_true, follows_pair, if_pos rfl,
    follows_pair, if_pos rfl]
  exact follows_listCode_get fields j x

theorem argument_codedNode_iff {U : ZFSet.{u}} {n : Nat}
    (fields : List ZFSet.{u}) (v : Fin n → ZFCarrier U) (j : Fin fields.length) (i : Fin n)
    (hji : fields.get j = natCode i.val) (x : ZFSet.{u}) :
    Argument (argumentPath j.val) (lookupSet U) (assignmentCodes U) Ordinal.omega0.toZFSet
      (codedNode fields v) x ↔ (v i).val = x := by
  constructor
  · rintro ⟨a, _, q, _, ha, hq, hx⟩
    have ha' : a = assignmentCode v := by
      rw [codedNode, follows_pair] at ha
      exact ha.symm
    have hq' : q = natCode i.val := (follows_codedNode_field fields v j q).mp hq |>.trans hji
    rw [ha', hq', mem_lookupSet_iff, lookup_assignment_iff] at hx
    exact hx
  · intro hx
    refine ⟨assignmentCode v,
      ZFSet.mem_range_self (f := fun a : PackedAssignment U => assignmentCode a.2) ⟨n, v⟩,
      natCode i.val, (mem_omega_iff_exists_natCode _).mpr ⟨i.val, rfl⟩,
      ?_, (follows_codedNode_field fields v j _).mpr hji.symm,
      (mem_lookupSet_iff U _ _ _).mpr ((lookup_assignment_iff v i x).mpr hx)⟩
    rw [codedNode, follows_pair]
    rfl

end OneYTruth.AtomicArgumentLookup
