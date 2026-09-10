import YesMetaZFC.BMS.WellFoundedness

/-!
# 任意 BM4 合法矩阵的展开良基性

上游的表示降界接口已适用于任意 `ValidArray`。本模块用高一行种子的展开
提供足够多的两两稳定标签，从而删除初始矩阵的 `Generated` 要求。

这里的良基关系是非平凡展开 `Step`，并非全部矩阵上的字典序。
-/

namespace ZeroY.BMS

open YesMetaZFC.BMS
open YesMetaZFC.BMS.StabilityFrame

universe u

/-- 只要已有有界稳定表示，标签上界的可达性便给出矩阵的可达性。 -/
theorem accessible_of_bounded_any {Label : Type u}
    {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) :
    ∀ {bound : Label}, Acc frame.lt bound →
      ∀ {array : ValidArray},
        ∀ representation : StableRepresentation frame array,
          representation.BoundedBy bound → Acc Step array := by
  intro bound hAccessible
  induction hAccessible with
  | intro bound hPredecessor ih =>
      intro array representation hBounded
      apply Acc.intro array
      intro smaller hStep
      rcases hStep.1 with ⟨index, hExpanded⟩
      subst smaller
      rcases system.expand_bounded index representation hBounded hStep.2 with
        ⟨smallerBound, hSmallerBound, expandedRepresentation,
          hExpandedBounded⟩
      exact ih smallerBound hSmallerBound expandedRepresentation hExpandedBounded

/-- 高一行的种子以第零列为坏根，最高父项行恰为给定高度。 -/
private def dominatingSeedContext (height : Nat) :
    ExpansionContext (validSeed (height + 1)) where
  lastIndex := 1
  maximalRow := height
  parentColumn := 0
  array_length := by simp [raw_validSeed, seed]
  maximal_row_eq := by
    simpa only [raw_validSeed] using maximalParentRow_seed_succ height
  parent_eq := by
    simpa only [raw_validSeed] using
      (parent_seed_one_of_lt (row := height) (height := height + 1)
        (Nat.lt_succ_self height))

/--
任意合法矩阵都有有界稳定表示。给目标的每一列使用种子展开中对应复制块
首列的标签；这些首列在目标的每个有效行上形成全祖先链。
-/
theorem exists_bounded_any {Label : Type u}
    {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) (array : ValidArray) :
    ∃ bound, ∃ representation : StableRepresentation frame array,
      representation.BoundedBy bound := by
  rcases rectangular_iff_exists_uniformHeight.mp array.rectangular_eq with
    ⟨height, hUniform⟩
  let context := dominatingSeedContext height
  have hGenerated : Generated
      ((validSeed (height + 1)).expand array.raw.length) :=
    .expand (.seed (height + 1)) array.raw.length
  rcases system.exists_bounded_of_generated hGenerated with
    ⟨bound, sourceRepresentation, hSourceBounded⟩
  let embed : Fin array.raw.length →
      Fin ((validSeed (height + 1)).expand array.raw.length).raw.length :=
    fun column =>
      ⟨context.copyPosition column.val 0,
        context.copyPosition_lt_length (Nat.le_of_lt column.isLt)
          context.blockLength_pos⟩
  let representation : StableRepresentation frame array := {
    label := fun column => sourceRepresentation.label (embed column)
    strictlyIncreasing := by
      intro left right hOrder
      apply sourceRepresentation.strictlyIncreasing
      change context.copyPosition left.val 0 < context.copyPosition right.val 0
      exact context.copyPosition_strictMono_copy hOrder
    preservesAncestor := by
      intro row left right hAncestor
      apply sourceRepresentation.preservesAncestor
      change isAncestor ((validSeed (height + 1)).expand array.raw.length).raw row
        (context.copyPosition left.val 0) (context.copyPosition right.val 0) = true
      apply context.first_copy_ancestor_of_lt
      · exact Nat.le_of_lt right.isLt
      · exact isAncestor_lt hAncestor
      · rcases ancestor_entries_lt hAncestor with
          ⟨leftValue, rightValue, hLeftEntry, hRightEntry, hEntryOrder⟩
        exact row_lt_uniformHeight_of_entry?_eq_some hUniform hLeftEntry
  }
  exact ⟨bound, representation, fun column => hSourceBounded (embed column)⟩

/-- 任意合法矩阵上的非平凡一步展开关系良基。 -/
theorem step_wellFounded_any {Label : Type u}
    {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) : WellFounded Step := by
  constructor
  intro array
  rcases exists_bounded_any system array with ⟨bound, representation, hBounded⟩
  exact accessible_of_bounded_any system (frame.lt_wellFounded.apply bound)
    representation hBounded

/-- 以良基关系方向书写的有限非空展开同样良基。 -/
theorem transGen_step_wellFounded_any {Label : Type u}
    {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) :
    WellFounded (Relation.TransGen Step) :=
  (step_wellFounded_any system).transGen

/-- 从任意同一起点展开得到的两个矩阵，在有限展开关系中可比。 -/
theorem descendants_comparable_any {Label : Type u}
    {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame)
    {root first second : ValidArray}
    (hFirst : ExpansionPath root first) (hSecond : ExpansionPath root second) :
    first = second ∨ StrictDescent first second ∨ StrictDescent second first :=
  expansionPath_endpoints_comparable_of_accessible
    ((step_wellFounded_any system).apply root) hFirst hSecond

end ZeroY.BMS
