import OneYTruth.AssignmentLookupFormula

/-!
# The entire finite-assignment lookup relation is constructible

Every stage is an actual bounded filter. Its full omega union is identified
with the genuine lookup relation, using exact head/tail transport and
induction on the assignment length.
-/

namespace OneYTruth.AssignmentLookup

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open Constructible.Model Constructible.Godel InternalNodes InternalProducts
open ConstructibleAssignmentCodes ConstructibleBoundedIteration ConstructibleDiagramSources
open CodedPaths
open Constructible.IndexedSequenceZF (mem_omega_iff_exists_natCode)

universe u

noncomputable def lookupBound (U : ZFSet.{u}) : ZFSet.{u} :=
  pairProduct (assignmentCodes U) (pairProduct Ordinal.omega0.toZFSet U)

theorem lookupBound_mem_L {U : ZFSet.{u}} (hU : U ∈ L) : lookupBound U ∈ L :=
  pairProduct_mem_L (assignmentCodes_mem_L hU) (pairProduct_mem_L omegaLCarrier.property hU)

theorem record_mem_lookupBound {U : ZFSet.{u}} {n : Nat}
    (v : Fin n → ZFCarrier U) (i : Fin n) :
    triple (assignmentCode v) (natCode i.val) (v i).val ∈ lookupBound U := by
  rw [lookupBound, pairProduct_eq_F2, pairProduct_eq_F2]
  exact mem_F2_iff.mpr ⟨assignmentCode v,
    ZFSet.mem_range_self (f := fun a : PackedAssignment U => assignmentCode a.2) ⟨n, v⟩,
    ZFSet.pair (natCode i.val) (v i).val,
    mem_F2_iff.mpr ⟨natCode i.val, (mem_omega_iff_exists_natCode _).mpr ⟨i.val, rfl⟩,
      (v i).val, (v i).property, rfl⟩, rfl⟩

noncomputable def lookupParams (U : LCarrier.{u}) : Tuple LCarrier.{u} 4 :=
  ![⟨lookupBound U.val, lookupBound_mem_L U.property⟩,
    ⟨assignmentCodes U.val, assignmentCodes_mem_L U.property⟩, omegaLCarrier, U]

noncomputable def lookupStages (U : LCarrier.{u}) : Nat → LCarrier.{u} :=
  uniformFiniteIterate (filterStep lookupFormula 0 (lookupParams U)) emptyLCarrier

theorem mem_lookupStages_succ_iff (U : LCarrier.{u}) (m : Nat) (z : ZFSet.{u}) :
    z ∈ (lookupStages U (m + 1)).val ↔ z ∈ lookupBound U.val ∧
      LookupRule (assignmentCodes U.val) Ordinal.omega0.toZFSet U.val (lookupStages U m).val z := by
  change z ∈ deltaSep lookupFormula
    (snoc (fun i => (lookupParams U i).val) (lookupStages U m).val) (lookupBound U.val) ↔ _
  rw [deltaSep, ZFSet.mem_sep]
  have hp : snoc (snoc (fun i => (lookupParams U i).val) (lookupStages U m).val) z =
      ![lookupBound U.val, assignmentCodes U.val, Ordinal.omega0.toZFSet,
        U.val, (lookupStages U m).val, z] := by
    funext i; fin_cases i <;> rfl
  rw [hp, satisfies_lookupFormula]

theorem lookupStages_sound (U : LCarrier.{u}) (m : Nat) :
    (lookupStages U m).val ⊆ lookupSet U.val := by
  induction m with
  | zero => intro z hz; exact (ZFSet.notMem_empty z hz).elim
  | succ m ih =>
    intro z hz
    obtain ⟨_, p, hp, i, _, x, _, c, hc, N, _, a, ha, hz, hscope, hhead, htail, hcase⟩ :=
      (mem_lookupStages_succ_iff U m z).mp hz
    rw [hz, mem_lookupSet_iff]
    apply lookup_transport hp hc ⟨a, ha⟩ hscope hhead htail
    exact hcase.imp_right (fun h => (mem_lookupSet_iff U.val c i x).mp (ih h))

theorem lookupStages_complete (U : LCarrier.{u}) (n : Nat)
    (v : Fin n → ZFCarrier U.val) (i : Fin n) :
    triple (assignmentCode v) (natCode i.val) (v i).val ∈ (lookupStages U n).val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hv : v = Fin.snoc (Fin.init v) (v (Fin.last n)) := (Fin.snoc_init_self v).symm
    rw [hv]
    let w := Fin.init v
    let a := v (Fin.last n)
    apply (mem_lookupStages_succ_iff U n _).mpr
    refine ⟨record_mem_lookupBound (Fin.snoc w a) i, ?_⟩
    apply lookupRule_snoc
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Or.inl ⟨rfl, by simp⟩
    · exact Or.inr (by simpa only [Fin.snoc_castSucc, Fin.val_castSucc] using ih w j)

noncomputable def lookupFamily (U : LCarrier.{u}) : ParametricUniformOmegaFamilySpec.{u} 5 :=
  family lookupFormula 0 (lookupParams U) emptyLCarrier

theorem lookupSet_mem_L {U : ZFSet.{u}} (hU : U ∈ L) : lookupSet U ∈ L := by
  let UL : LCarrier.{u} := ⟨U, hU⟩
  let unionL := parametricUniformOmegaUnion (lookupFamily UL)
  have heq : unionL.val = lookupSet U := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨m, hm⟩ := (mem_parametricUniformOmegaUnion_iff (lookupFamily UL)
        ⟨z, mem_L_of_mem hz unionL.property⟩).mp hz
      exact lookupStages_sound UL m hm
    · intro hz
      obtain ⟨⟨n, v, i⟩, rfl⟩ := ZFSet.mem_range.mp hz
      have hmem := lookupStages_complete UL n v i
      exact (mem_parametricUniformOmegaUnion_iff (lookupFamily UL)
        ⟨witnessCode ⟨n, v, i⟩, mem_L_of_mem hmem (lookupStages UL n).property⟩).mpr ⟨n, hmem⟩
  rw [← heq]
  exact unionL.property

end OneYTruth.AssignmentLookup
