import OneYTruth.ConstructibleListCodes

/-!
# Uniform iteration of a displayed bounded filter in L

Every step is the actual separated subset of a fixed constructible bound.
A displayed bounded graph formula defines that operation, so the proved
uniform finite-iteration theorem collects its entire omega family.
-/

namespace OneYTruth.ConstructibleBoundedIteration

open Constructible Constructible.Delta0Formula Constructible.Model

universe u

noncomputable def deltaSep {p : Nat} (φ : Delta0Formula (p + 1))
    (params : Tuple ZFSet.{u} p) (B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => Satisfies ZFMem φ (snoc params x)) B

theorem deltaSep_mem_L {p : Nat} (φ : Delta0Formula (p + 1))
    (params : Tuple LCarrier.{u} p) (B : LCarrier.{u}) :
    deltaSep φ (fun i => (params i).val) B.val ∈ L := by
  obtain ⟨T, hT⟩ := exists_separationLCarrier φ.toFO params B
  have heq : T.val = deltaSep φ (fun i => (params i).val) B.val := by
    apply ZFSet.ext
    intro x
    have hsem (xL : LCarrier.{u}) :
        FOFormula.Satisfies lCarrierMem φ.toFO (snoc params xL) ↔
        Satisfies ZFMem φ (snoc (fun i => (params i).val) xL.val) := by
      rw [Delta0Formula.satisfies_toFO_lCarrier_absolute, Delta0Formula.satisfies_toFO]
      rw [Model.subtypeVal_snoc]
    constructor
    · intro hx
      let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx T.property⟩
      obtain ⟨hxB, hφ⟩ := (hT xL).mp hx
      exact ZFSet.mem_sep.mpr ⟨hxB, (hsem xL).mp hφ⟩
    · intro hx
      obtain ⟨hxB, hφ⟩ := ZFSet.mem_sep.mp hx
      let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hxB B.property⟩
      exact (hT xL).mpr ⟨hxB, (hsem xL).mpr hφ⟩
  rw [← heq]
  exact T.property

def filterReindex (p : Nat) : Fin (p + 2) → Fin (p + 3) :=
  Fin.lastCases (Fin.last (p + 2)) (fun i => i.castSucc.castSucc)

theorem satisfies_filterReindex {p : Nat} (φ : Delta0Formula (p + 2))
    (params : Tuple ZFSet.{u} p) (S T x : ZFSet.{u}) :
    Satisfies ZFMem (φ.rename (filterReindex p)) (snoc (snoc (snoc params S) T) x) ↔
      Satisfies ZFMem φ (snoc (snoc params S) x) := by
  rw [satisfies_rename]
  have heq : (fun i => snoc (snoc (snoc params S) T) x (filterReindex p i)) =
      snoc (snoc params S) x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [filterReindex]
    · simp [filterReindex]
  rw [heq]

def filterGraph {p : Nat} (φ : Delta0Formula (p + 2)) (bound : Fin p) :
    Delta0Formula (p + 2) :=
  .conj
    (.boundedAll (Fin.last (p + 1))
      (.conj (.mem (Fin.last (p + 2)) bound.castSucc.castSucc.castSucc)
        (φ.rename (filterReindex p))))
    (.boundedAll bound.castSucc.castSucc
      (.imp (φ.rename (filterReindex p))
        (.mem (Fin.last (p + 2)) (Fin.last (p + 1)).castSucc)))

theorem satisfies_filterGraph {p : Nat} (φ : Delta0Formula (p + 2)) (bound : Fin p)
    (params : Tuple ZFSet.{u} p) (S T : ZFSet.{u}) :
    Satisfies ZFMem (filterGraph φ bound) (snoc (snoc params S) T) ↔
      T = deltaSep φ (snoc params S) (params bound) := by
  simp only [filterGraph, Satisfies, satisfies_boundedAll, satisfies_imp,
    satisfies_filterReindex, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hout, hin⟩
    apply ZFSet.ext
    intro x
    rw [deltaSep, ZFSet.mem_sep]
    exact ⟨hout x, fun h => hin x h.1 h.2⟩
  · rintro rfl
    constructor
    · intro x hx
      exact ZFSet.mem_sep.mp hx
    · intro x hx hφ
      exact ZFSet.mem_sep.mpr ⟨hx, hφ⟩

noncomputable def filterStep {p : Nat} (φ : Delta0Formula (p + 2)) (bound : Fin p)
    (params : Tuple LCarrier.{u} p) (S : LCarrier.{u}) : LCarrier.{u} :=
  ⟨deltaSep φ (snoc (fun i => (params i).val) S.val) (params bound).val,
    by simpa only [Model.subtypeVal_snoc] using deltaSep_mem_L φ (snoc params S) (params bound)⟩

theorem filterStep_defines {p : Nat} (φ : Delta0Formula (p + 2)) (bound : Fin p)
    (params : Tuple LCarrier.{u} p) :
    DefinesFiniteIterationStep (filterGraph φ bound).toFO params (filterStep φ bound params) := by
  intro S T
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute, Delta0Formula.satisfies_toFO,
    Model.subtypeVal_snoc, Model.subtypeVal_snoc, satisfies_filterGraph]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

noncomputable def family {p : Nat} (φ : Delta0Formula (p + 2)) (bound : Fin p)
    (params : Tuple LCarrier.{u} p) (initial : LCarrier.{u}) :
    ParametricUniformOmegaFamilySpec.{u} (p + 1) :=
  uniformFiniteIterationOmegaFamilySpec (filterGraph φ bound).toFO params
    (filterStep φ bound params) initial (filterStep_defines φ bound params)

end OneYTruth.ConstructibleBoundedIteration
