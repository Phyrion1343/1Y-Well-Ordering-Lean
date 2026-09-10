import OneYTruth.ConstructibleListCodes

/-!
# The complete assignment-code set belongs to L

The length field is checked by one displayed first-order formula: a payload
has length n precisely when it enters the list construction at stage n+1.
Separation on omega times the complete constructible list-code set supplies
all length-labelled sequence codes. The final identification uses the actual
reverse-order assignment convention.
-/

namespace OneYTruth.ConstructibleAssignmentCodes

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open Constructible.Model Constructible.Godel ConstructibleListCodes InternalNodes

universe u

def listStageFormula : FOFormula 5 := uniformFiniteIterationFormula listStepFormula.toFO

/-- Parameters U,zero,initial; candidate code; witnesses index,payload,successor,current,next. -/
def sequenceCodeMatrix : FOFormula 9 :=
  .conj (kuratowskiPairEqAt 3 4 5).toFO
    (.conj (successorFOAt 6 4)
      (.conj (finiteIterationStepFormulaAt listStageFormula ![0, 1, 2] 4 7)
        (.conj (finiteIterationStepFormulaAt listStageFormula ![0, 1, 2] 6 8)
          (.conj (.mem 5 8) (.neg (.mem 5 7))))))

theorem satisfies_sequenceCodeMatrix (s : Tuple LCarrier.{u} 9) :
    FOFormula.Satisfies lCarrierMem sequenceCodeMatrix s ↔
      (s 3).val = ZFSet.pair (s 4).val (s 5).val ∧
      (s 6).val = insert (s 4).val (s 4).val ∧
      FOFormula.Satisfies lCarrierMem listStageFormula
        (snoc (snoc (fun i => s (![0, 1, 2] i)) (s 4)) (s 7)) ∧
      FOFormula.Satisfies lCarrierMem listStageFormula
        (snoc (snoc (fun i => s (![0, 1, 2] i)) (s 6)) (s 8)) ∧
      (s 5).val ∈ (s 8).val ∧ (s 5).val ∉ (s 7).val := by
  simp only [sequenceCodeMatrix, FOFormula.Satisfies,
    satisfies_kuratowskiPairEqAt_lCarrier_generic, satisfies_successorFOAt_lCarrier,
    satisfies_finiteIterationStepFormulaAt, lCarrierMem]

attribute [irreducible] sequenceCodeMatrix

def sequenceCodeFormula : FOFormula 4 := .ex (.ex (.ex (.ex (.ex sequenceCodeMatrix))))

theorem satisfies_sequenceCodeFormula (U : LCarrier.{u}) (n : Nat) (p : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem sequenceCodeFormula
      (snoc (listFamilySpec U).params (orderedPairLCarrier (natLCarrier n) p)) ↔
      p.val ∈ (listStages U (n + 1)).val ∧ p.val ∉ (listStages U n).val := by
  have hsem : FOFormula.Satisfies lCarrierMem sequenceCodeFormula
      (snoc (listFamilySpec U).params (orderedPairLCarrier (natLCarrier n) p)) ↔
      ∃ i q j A B : LCarrier.{u},
        ZFSet.pair (natCode n) p.val = ZFSet.pair i.val q.val ∧
        j.val = insert i.val i.val ∧
        FOFormula.Satisfies lCarrierMem listStageFormula
          (snoc (snoc (listFamilySpec U).params i) A) ∧
        FOFormula.Satisfies lCarrierMem listStageFormula
          (snoc (snoc (listFamilySpec U).params j) B) ∧
        q.val ∈ B.val ∧ q.val ∉ A.val := by
    have hparams : (listFamilySpec U).params = ![U, emptyLCarrier, emptyLCarrier] := by
      funext i
      fin_cases i <;> rfl
    rw [hparams]
    simp only [sequenceCodeFormula, FOFormula.Satisfies, satisfies_sequenceCodeMatrix]
    simp only [constructible_snoc_eq, Fin.snoc, Fin.castLT]
    change (∃ i q j A B : LCarrier.{u},
      ZFSet.pair (natCode n) p.val = ZFSet.pair i.val q.val ∧
      j.val = insert i.val i.val ∧
      FOFormula.Satisfies lCarrierMem listStageFormula
        (snoc (snoc ![U, emptyLCarrier, emptyLCarrier] i) A) ∧
      FOFormula.Satisfies lCarrierMem listStageFormula
        (snoc (snoc ![U, emptyLCarrier, emptyLCarrier] j) B) ∧
      q.val ∈ B.val ∧ q.val ∉ A.val) ↔ _
    rfl
  rw [hsem]
  constructor
  · rintro ⟨i, q, j, A, B, hpair, hj, hA, hB, hqB, hqA⟩
    obtain ⟨hi, hq⟩ := ZFSet.pair_inj.mp hpair
    have hi' : i = natLCarrier n := Subtype.ext hi.symm
    have hq' : q = p := Subtype.ext hq.symm
    subst i q
    have hj' : j = natLCarrier (n + 1) :=
      Subtype.ext (hj.trans (natCode_succ_eq_insert n).symm)
    subst j
    have hA' : A = listStages U n := (listFamilySpec U).realizes n A |>.mp hA
    have hB' : B = listStages U (n + 1) := (listFamilySpec U).realizes (n + 1) B |>.mp hB
    subst A B
    exact ⟨hqB, hqA⟩
  · rintro ⟨hpB, hpA⟩
    refine ⟨natLCarrier n, p, natLCarrier (n + 1), listStages U n,
      listStages U (n + 1), rfl, natCode_succ_eq_insert n, ?_, ?_, hpB, hpA⟩
    · exact (listFamilySpec U).realizes n (listStages U n) |>.mpr rfl
    · exact (listFamilySpec U).realizes (n + 1) (listStages U (n + 1)) |>.mpr rfl

theorem exact_listStage_iff (U : LCarrier.{u}) (n : Nat) (p : ZFSet.{u}) :
    (p ∈ (listStages U (n + 1)).val ∧ p ∉ (listStages U n).val) ↔
      ∃ xs : List (ZFCarrier U.val), xs.length = n ∧ p = listCode (xs.map Subtype.val) := by
  rw [mem_listStages_iff, mem_listStages_iff]
  constructor
  · rintro ⟨⟨xs, hx, hp⟩, hnot⟩
    refine ⟨xs, ?_, hp⟩
    have : ¬xs.length < n := fun h => hnot ⟨xs, h, hp⟩
    omega
  · rintro ⟨xs, hx, hp⟩
    refine ⟨⟨xs, by omega, hp⟩, ?_⟩
    rintro ⟨ys, hy, hpy⟩
    have heq := listCode_injective (hp.symm.trans hpy)
    have hlen := congrArg List.length heq
    simp only [List.length_map] at hlen
    omega

noncomputable def sequenceCodes (U : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun xs : List (ZFCarrier U) => sequenceCode (xs.map Subtype.val))

theorem sequenceCodes_mem_L {U : ZFSet.{u}} (hU : U ∈ L) : sequenceCodes U ∈ L := by
  let UL : LCarrier.{u} := ⟨U, hU⟩
  let base : LCarrier.{u} := ⟨F2 omegaLCarrier.val (listCodes U),
    op_mem_L (i := 2) omegaLCarrier.property (listCodes_mem_L hU)⟩
  obtain ⟨S, hS⟩ := exists_separationLCarrier sequenceCodeFormula (listFamilySpec UL).params base
  have heq : S.val = sequenceCodes U := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      let zL : LCarrier.{u} := ⟨z, mem_L_of_mem hz S.property⟩
      obtain ⟨hzbase, hzformula⟩ := (hS zL).mp hz
      change z ∈ F2 omegaLCarrier.val (listCodes U) at hzbase
      obtain ⟨i, hi, p, hp, hzip⟩ := mem_F2_iff.mp hzbase
      obtain ⟨n, hin⟩ := (IndexedSequenceZF.mem_omega_iff_exists_natCode i).mp hi
      let pL : LCarrier.{u} := ⟨p, mem_L_of_mem hp (listCodes_mem_L hU)⟩
      have hzL : zL = orderedPairLCarrier (natLCarrier n) pL :=
        Subtype.ext (hzip.trans (congrArg (fun i => ZFSet.pair i p) hin))
      rw [hzL, satisfies_sequenceCodeFormula, exact_listStage_iff] at hzformula
      obtain ⟨xs, hx, hpx⟩ := hzformula
      refine ZFSet.mem_range.mpr ⟨xs, ?_⟩
      simp only [sequenceCode, List.length_map, hx]
      exact (hzip.trans (congrArg₂ ZFSet.pair hin hpx)).symm
    · intro hz
      obtain ⟨xs, hxs⟩ := ZFSet.mem_range.mp hz
      have hpL : listCode (xs.map Subtype.val) ∈ L := by
        apply listCode_mem_L
        intro a ha
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
        exact mem_L_of_mem a.property hU
      let pL : LCarrier.{u} := ⟨listCode (xs.map Subtype.val), hpL⟩
      let zL := orderedPairLCarrier (natLCarrier xs.length) pL
      have hzL : zL.val = z := by simpa [zL, pL, sequenceCode] using hxs
      rw [← hzL]
      apply (hS zL).mpr
      constructor
      · change zL.val ∈ F2 omegaLCarrier.val (listCodes U)
        apply mem_F2_iff.mpr
        refine ⟨natCode xs.length, ?_, pL.val, ?_, rfl⟩
        · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨xs.length, rfl⟩
        · exact ZFSet.mem_range_self (f := fun xs : List (ZFCarrier U) =>
            listCode (xs.map Subtype.val)) xs
      · rw [satisfies_sequenceCodeFormula, exact_listStage_iff]
        exact ⟨xs, rfl, rfl⟩
  rw [← heq]
  exact S.property

theorem assignmentCodes_eq_sequenceCodes (U : ZFSet.{u}) : assignmentCodes U = sequenceCodes U := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨⟨n, v⟩, hv⟩ := ZFSet.mem_range.mp hz
    refine ZFSet.mem_range.mpr ⟨(List.ofFn v).reverse, ?_⟩
    simpa only [assignmentCode, List.map_reverse, List.map_ofFn, Function.comp_def] using hv
  · intro hz
    obtain ⟨xs, hxs⟩ := ZFSet.mem_range.mp hz
    let v : Fin xs.reverse.length → ZFCarrier U := xs.reverse.get
    refine ZFSet.mem_range.mpr ⟨⟨xs.reverse.length, v⟩, ?_⟩
    have hv : List.ofFn v = xs.reverse := List.ofFn_get xs.reverse
    have hmap : List.ofFn (fun i => (v i).val) = xs.reverse.map Subtype.val := by
      calc
        _ = (List.ofFn v).map Subtype.val := by rw [List.map_ofFn]; rfl
        _ = _ := congrArg (List.map Subtype.val) hv
    change sequenceCode (List.ofFn (fun i => (v i).val)).reverse = z
    rw [hmap, List.map_reverse, List.reverse_reverse]
    exact hxs

theorem assignmentCodes_mem_L {U : ZFSet.{u}} (hU : U ∈ L) : assignmentCodes U ∈ L := by
  rw [assignmentCodes_eq_sequenceCodes]
  exact sequenceCodes_mem_L hU

end OneYTruth.ConstructibleAssignmentCodes
