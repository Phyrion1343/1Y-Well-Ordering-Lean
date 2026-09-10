import ZeroY.Dynamics.Prefix
import ZeroY.Seed

/-!
# 实际展开路径、标准生成集及固定起点的同构

载体由各自算法独立生成，再由已证明的全域展开交换建立对应。
-/

namespace ZeroY

open YesMetaZFC.BMS
open YesMetaZFC.BMS.StabilityFrame

theorem encode_yPath {root s : Expr} (hPath : YExpansionPath root s) :
    ExpansionPath (encode root) (encode s) := by
  induction hPath with
  | refl => exact .refl _
  | tail prior index ih =>
      exact .tail ih ⟨index, encode_expandY _ _⟩

theorem bms_path_y_preimage {root : Expr} {array : ValidArray}
    (hPath : ExpansionPath (encode root) array) :
    ∃ s, YExpansionPath root s ∧ encode s = array := by
  induction hPath with
  | refl => exact ⟨root, .refl _, rfl⟩
  | tail prior edge ih =>
      obtain ⟨s, hPrior, hEncode⟩ := ih
      obtain ⟨index, rfl⟩ := edge
      exact ⟨expandY s index, .tail hPrior index, by rw [encode_expandY, hEncode]⟩

theorem encode_path_iff (root s : Expr) :
    ExpansionPath (encode root) (encode s) ↔ YExpansionPath root s := by
  constructor
  · intro hPath
    obtain ⟨t, hPath, hEqual⟩ := bms_path_y_preimage hPath
    have hSame := encode_injective hEqual
    simpa only [hSame] using hPath
  · exact encode_yPath

theorem generated_encode {s : Expr} (hGenerated : YGenerated s) : Generated (encode s) := by
  induction hGenerated with
  | seed height => rw [encode_seed]; exact .seed height
  | expand prior index ih => rw [encode_expandY]; exact .expand ih index

theorem bms_generated_y_preimage {array : ValidArray} (hGenerated : Generated array) :
    ∃ s, YGenerated s ∧ encode s = array := by
  induction hGenerated with
  | seed height => exact ⟨Expr.seed height, .seed height, encode_seed height⟩
  | expand prior index ih =>
      obtain ⟨s, hPrior, hEncode⟩ := ih
      exact ⟨expandY s index, .expand hPrior index, by rw [encode_expandY, hEncode]⟩

theorem generated_encode_iff (s : Expr) : Generated (encode s) ↔ YGenerated s := by
  constructor
  · intro hGenerated
    obtain ⟨t, hT, hEqual⟩ := bms_generated_y_preimage hGenerated
    have hSame := encode_injective hEqual
    simpa only [hSame] using hT
  · exact generated_encode

theorem expandY_seed_succ_one (height : Nat) :
    expandY (Expr.seed (height + 1)) 1 = Expr.seed height := by
  apply encode_injective
  rw [encode_expandY, encode_seed, encode_seed]
  exact validSeed_succ_expand_one height

/-- 零高度种子已从正高度种子生成，故与通常只取正高度的定义完全相同。 -/
theorem yGenerated_iff_positive_seed_path (s : Expr) :
    YGenerated s ↔ ∃ height, 0 < height ∧ YExpansionPath (Expr.seed height) s := by
  rw [yGenerated_iff_seed_path]
  constructor
  · rintro ⟨height, hPath⟩
    cases height with
    | zero =>
        refine ⟨1, by decide, ?_⟩
        have hSeedPath : YExpansionPath (Expr.seed 1) (Expr.seed 0) := by
          rw [← expandY_seed_succ_one 0]
          exact .single _ _
        exact hSeedPath.trans hPath
    | succ height => exact ⟨height + 1, by omega, hPath⟩
  · rintro ⟨height, _, hPath⟩
    exact ⟨height, hPath⟩

theorem generated_roundTrip {array : ValidArray} (hGenerated : Generated array) :
    RoundTrip array.raw := by
  obtain ⟨s, _, rfl⟩ := bms_generated_y_preimage hGenerated
  exact encode_roundTrip s

def generatedEncode (s : YGeneratedExpr) : GeneratedArray := ⟨encode s.1, generated_encode s.2⟩

def generatedDecode (array : GeneratedArray) : YGeneratedExpr := ⟨decode array.1, by
  obtain ⟨s, hGenerated, hEncode⟩ := bms_generated_y_preimage array.2
  rw [← hEncode, decode_encode]
  exact hGenerated⟩

def generatedOrderIso :
    StrictRelationIso YGeneratedExpr GeneratedArray YGeneratedLt BMS.GeneratedMatrixLt where
  toFun := generatedEncode
  invFun := generatedDecode
  left_inv := fun s => Subtype.ext (decode_encode s.1)
  right_inv := fun array => Subtype.ext
    (encode_decode_of_structural array.1 (structural_of_roundTrip _ (generated_roundTrip array.2)))
  rel_iff := fun s t => encode_lt_iff s.1 t.1

def descendantEncode {root : Expr} (s : YDescendant root) : BMS.Descendant (encode root) :=
  ⟨encode s.1, encode_yPath s.2⟩

def descendantDecode {root : Expr} (array : BMS.Descendant (encode root)) : YDescendant root :=
  ⟨decode array.1, by
    obtain ⟨s, hPath, hEncode⟩ := bms_path_y_preimage array.2
    rw [← hEncode, decode_encode]
    exact hPath⟩

def descendantOrderIso (root : Expr) :
    StrictRelationIso (YDescendant root) (BMS.Descendant (encode root))
      YDescendantLt BMS.DescendantLt where
  toFun := descendantEncode
  invFun := descendantDecode
  left_inv := fun s => Subtype.ext (decode_encode s.1)
  right_inv := by
    intro array
    apply Subtype.ext
    obtain ⟨s, _, hEncode⟩ := bms_path_y_preimage array.2
    change encode (decode array.1) = array.1
    rw [← hEncode, decode_encode]
  rel_iff := fun s t => encode_lt_iff s.1 t.1

theorem encode_step_iff (smaller larger : Expr) :
    Step (encode smaller) (encode larger) ↔ YStep smaller larger := by
  constructor
  · rintro ⟨⟨index, hExpanded⟩, hDifferent⟩
    refine ⟨⟨index, encode_injective ?_⟩, ?_⟩
    · rw [encode_expandY]
      exact hExpanded.symm
    · intro hSame
      exact hDifferent (congrArg encode hSame)
  · rintro ⟨⟨index, hExpanded⟩, hDifferent⟩
    refine ⟨⟨index, ?_⟩, fun hSame => hDifferent (encode_injective hSame)⟩
    rw [← encode_expandY, hExpanded]

universe u

theorem yStep_wellFounded {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) : WellFounded YStep :=
  wellFounded_of_relation_map encode (fun h => (encode_step_iff _ _).mpr h)
    (BMS.step_wellFounded_any system)

theorem yGenerated_strictWellOrder {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) : StrictWellOrder YGeneratedExpr YGeneratedLt where
  wellFounded := generatedOrderIso.wellFounded_iff.mpr
    (BMS.generatedMatrix_strictWellOrder system).wellFounded
  transitive := fun hFirst hSecond => exprLt_trans hFirst hSecond
  trichotomy := by
    intro first second
    rcases exprLt_trichotomy first.1 second.1 with hEqual | hLess | hGreater
    · exact Or.inl (Subtype.ext hEqual)
    · exact Or.inr (Or.inl hLess)
    · exact Or.inr (Or.inr hGreater)

theorem yDescendants_strictWellOrder {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) (root : Expr) :
    StrictWellOrder (YDescendant root) YDescendantLt where
  wellFounded := (descendantOrderIso root).wellFounded_iff.mpr
    (BMS.descendants_strictWellOrder system (encode root)).wellFounded
  transitive := fun hFirst hSecond => exprLt_trans hFirst hSecond
  trichotomy := by
    intro first second
    rcases exprLt_trichotomy first.1 second.1 with hEqual | hLess | hGreater
    · exact Or.inl (Subtype.ext hEqual)
    · exact Or.inr (Or.inl hLess)
    · exact Or.inr (Or.inr hGreater)

theorem no_infinite_yStep_chain {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) :
    ¬ ∃ chain : Nat → Expr, ∀ index, YStep (chain (index + 1)) (chain index) := by
  rintro ⟨chain, hStep⟩
  have hNoChain : ∀ s, Acc YStep s → ∀ index, chain index ≠ s := by
    intro s hAcc
    induction hAcc with
    | intro s _ ih =>
        intro index hEqual
        apply ih (chain (index + 1))
        · rw [← hEqual]
          exact hStep index
        · rfl
  exact hNoChain _ ((yStep_wellFounded system).apply (chain 0)) 0 rfl

end ZeroY
