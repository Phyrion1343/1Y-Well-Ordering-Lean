import ZeroY.Expansion.Prefix
import ZeroY.Expansion.CopyRows
import ZeroY.Dynamics.Definitions
import ZeroY.Dynamics.Prefix
import ZeroY.Expansion.Conjugacy
import ZeroY.Expansion.LastColumn

/-!
# Wiki 端点约定

参数 index 表示 Wiki 的 q=index+1，避免给未定义的 q=0 任意赋值。
最高活动行有坏块长度 L、原末列位置 c 时，W_q 是同一无限复制山脉的
前 c+1+(q-1)L 项，即完整坏块算法 E_q 的指定前缀。HTML 完整坏块模式
E_n 的有限端点为 c+nL；两者不能按同下标逐项等同。
-/

namespace ZeroY

/-- Wiki 端点长度；无活动行时仍按原规则删除末项。 -/
def wikiLength (s : Sequence) (index : Nat) : Nat :=
  match expansionSite s with
  | none => s.length - 1
  | some (_, root) => (s.length - 1) + 1 + index * ((s.length - 1) - root)

/-- Wiki 展开使用独立数值山脉的有限端点，不通过 BMS 定义。 -/
def expandWikiRaw (s : Sequence) (index : Nat) : Sequence :=
  (expandYRaw s (index + 1)).take (wikiLength s index)

theorem expandWikiRaw_legal {s : Sequence} (hLegal : Legal s) (index : Nat) :
    Legal (expandWikiRaw s index) :=
  legal_take (expandYRaw_legal hLegal (index + 1)) _

def expandWiki (s : Expr) (index : Nat) : Expr :=
  ⟨expandWikiRaw s.values index, expandWikiRaw_legal s.legal index⟩

@[simp]
theorem expandWiki_values (s : Expr) (index : Nat) :
    (expandWiki s index).values = expandWikiRaw s.values index := rfl

theorem expandWiki_eq_take (s : Expr) (index : Nat) :
    expandWiki s index = (expandY s (index + 1)).take (wikiLength s.values index) := rfl

theorem expandWiki_eq_take_of_no_site (s : Expr) (index : Nat)
    (hNone : expansionSite s.values = none) :
    expandWiki s index = s.take (s.values.length - 1) := by
  apply Expr.ext
  simp only [expandWiki_values, expandWikiRaw, wikiLength, expandYRaw, hNone,
    List.take_take, Nat.min_self, Expr.take]

/-- 左向求和与任何有限前缀截断交换。 -/
theorem sumRow_take (parent : ParentMap) (upper : Sequence) (count : Nat) :
    (sumRow parent upper).take count = sumRow parent (upper.take count) := by
  apply List.ext_getElem (by simp [sumRow_length])
  intro column hLeft hRight
  have hColumn : column < (upper.take count).length := by
    simpa only [sumRow_length] using hRight
  have hOriginal : column < (sumRow parent upper).length := by
    simp only [List.length_take] at hLeft
    omega
  have hCount : column < count := by
    simp only [List.length_take] at hLeft
    omega
  have h := sumRow_getD_prefix parent upper hColumn
  simpa only [List.getElem?_eq_getElem hOriginal, List.getElem?_eq_getElem hRight,
    Option.getD_some, List.getElem_take] using h

theorem sumRow_foldr_take (parents : Nat → ParentMap) (rows : List Nat)
    (upper : Sequence) (count : Nat) :
    (rows.foldr (fun row next => sumRow (parents row) next) upper).take count =
      rows.foldr (fun row next => sumRow (parents row) next) (upper.take count) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.foldr_cons, sumRow_take, ih]

/-- 增加完整复制块只在末尾追加山脉数值。 -/
theorem expandYRaw_take_next (s : Sequence) (count : Nat) :
    (expandYRaw s (count + 1)).take (expandYRaw s count).length = expandYRaw s count := by
  unfold expandYRaw
  cases hSite : expansionSite s with
  | none => exact List.take_length
  | some site =>
      rcases site with ⟨row, root⟩
      simp only
      rw [sumRow_foldr_length, sumRow_foldr_take, copyMountainRow_succ,
        List.take_append_length]

theorem expandY_take_next (s : Expr) (count : Nat) :
    (expandY s (count + 1)).take (expandY s count).values.length = expandY s count := by
  apply Expr.ext
  exact expandYRaw_take_next s.values count

theorem expandYRaw_length_of_site {s : Sequence} {row root : Nat}
    (hSite : expansionSite s = some (row, root)) (count : Nat) :
    (expandYRaw s count).length = (s.length - 1) + count * ((s.length - 1) - root) := by
  have hRoot := expansionSite_root_lt hSite
  unfold expandYRaw
  rw [hSite]
  simp only
  rw [sumRow_foldr_length, copyMountainRow_length]
  · simp only [mountainLayer, layerAfter_length]
    omega
  · omega

theorem expandYRaw_length_le_wikiLength (s : Sequence) (index : Nat) :
    (expandYRaw s index).length ≤ wikiLength s index := by
  cases hSite : expansionSite s with
  | none => simp [expandYRaw, wikiLength, hSite]
  | some site =>
      rcases site with ⟨row, root⟩
      rw [expandYRaw_length_of_site hSite]
      simp only [wikiLength, hSite]
      omega

/-- E_n 是 W_(n+1) 的前缀，包含两种端点相差一项的情形。 -/
theorem expandY_eq_wiki_take (s : Expr) (index : Nat) :
    (expandWiki s index).take (expandY s index).values.length = expandY s index := by
  apply Expr.ext
  change ((expandYRaw s.values (index + 1)).take (wikiLength s.values index)).take
    (expandYRaw s.values index).length = expandYRaw s.values index
  rw [List.take_take, Nat.min_eq_left (expandYRaw_length_le_wikiLength s.values index),
    expandYRaw_take_next]

theorem expr_take_eq_self (s : Expr) {count : Nat} (hCount : s.values.length ≤ count) :
    s.take count = s := by
  apply Expr.ext
  exact List.take_of_length_le hCount

/-- 任一含删尾步骤的自反传递可达关系，自动包含全部有限前缀。 -/
theorem prefix_reachable_of_delete (reach : Expr → Expr → Prop)
    (hRefl : ∀ s, reach s s)
    (hTrans : ∀ {a b c}, reach a b → reach b c → reach a c)
    (hDelete : ∀ s, reach s (s.take (s.values.length - 1)))
    (s : Expr) (count : Nat) : reach s (s.take count) := by
  have hBounded : ∀ size, ∀ s : Expr, s.values.length = size → reach s (s.take count) := by
    intro size
    induction size using Nat.strongRecOn with
    | ind size ih =>
        intro current hSize
        by_cases hCount : current.values.length ≤ count
        · rw [expr_take_eq_self current hCount]
          exact hRefl current
        · let shorter := current.take (current.values.length - 1)
          have hShorterLength : shorter.values.length = current.values.length - 1 := by
            simp [shorter, Expr.take, List.length_take, Nat.min_eq_left (by omega :
              current.values.length - 1 ≤ current.values.length)]
          have hSmaller : shorter.values.length < size := by omega
          have hNext := ih shorter.values.length hSmaller shorter rfl
          have hNextTarget : shorter.take count = current.take count := by
            rw [show shorter = current.take (current.values.length - 1) from rfl,
              expr_take_take, Nat.min_eq_left (by omega : count ≤ current.values.length - 1)]
          rw [hNextTarget] at hNext
          exact hTrans (hDelete current) hNext
  exact hBounded s.values.length s rfl

/-- 每次 Wiki 展开由一次完整块展开及有限删尾得到。 -/
theorem yExpansionPath_expandWiki (s : Expr) (index : Nat) : YExpansionPath s (expandWiki s index) := by
  rw [expandWiki_eq_take]
  exact (YExpansionPath.single s (index + 1)).trans (yPath_take _ _)

/-- Wiki 有限展开路径直接由 Wiki 的数值算法生成。 -/
inductive WikiExpansionPath : Expr → Expr → Prop
  | refl (s : Expr) : WikiExpansionPath s s
  | tail {root middle : Expr} (prior : WikiExpansionPath root middle) (index : Nat) :
      WikiExpansionPath root (expandWiki middle index)

namespace WikiExpansionPath

theorem single (s : Expr) (index : Nat) : WikiExpansionPath s (expandWiki s index) :=
  .tail (.refl s) index

theorem trans {first second third : Expr} (left : WikiExpansionPath first second)
    (right : WikiExpansionPath second third) : WikiExpansionPath first third := by
  induction right with
  | refl => exact left
  | tail prior index ih => exact .tail ih index

end WikiExpansionPath

inductive WikiGenerated : Expr → Prop
  | seed (height : Nat) : WikiGenerated (Expr.seed height)
  | expand {s : Expr} (prior : WikiGenerated s) (index : Nat) : WikiGenerated (expandWiki s index)

abbrev WikiStep := ExpansionStep expandWiki

theorem wikiGenerated_of_path {root s : Expr} (hRoot : WikiGenerated root)
    (hPath : WikiExpansionPath root s) : WikiGenerated s := by
  induction hPath with
  | refl => exact hRoot
  | tail prior index ih => exact .expand ih index

/-- Wiki 的 q=1 在有活动行时保留原前缀，并把实际末项恰减一。 -/
theorem expandWiki_zero_values_of_context (s : Expr)
    (context : YesMetaZFC.BMS.ExpansionContext (encode s)) :
    (expandWiki s 0).values = s.values.take context.lastIndex ++
      [s.values[context.lastIndex]?.getD 0 - 1] := by
  have hLength : s.values.length = context.lastIndex + 1 := by
    simpa only [encode_length] using context.array_length
  have hLast : s.values.length - 1 = context.lastIndex := by omega
  have hSite := expansionSite_of_context s context
  have hExpanded : context.lastIndex < (expandYRaw s.values 1).length := by
    rw [expandYRaw_length_of_site hSite]
    have := context.parentColumn_lt_lastIndex
    rw [hLast]
    omega
  change (expandYRaw s.values 1).take (wikiLength s.values 0) = _
  simp only [wikiLength, hSite, Nat.zero_mul, Nat.add_zero, hLast]
  rw [List.take_succ_eq_append_getElem hExpanded, expandYRaw_take_last_of_context s context 1]
  have hValue := expandYRaw_newroot_of_context s context (by omega : 0 < 1)
  rw [List.getElem?_eq_getElem hExpanded, Option.getD_some] at hValue
  rw [hValue]

theorem expandWiki_zero_length_of_context (s : Expr)
    (context : YesMetaZFC.BMS.ExpansionContext (encode s)) :
    (expandWiki s 0).values.length = s.values.length := by
  have hLength : s.values.length = context.lastIndex + 1 := by
    simpa only [encode_length] using context.array_length
  rw [expandWiki_zero_values_of_context s context]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_take,
    Nat.min_eq_left (by omega : context.lastIndex ≤ s.values.length)]
  omega

theorem expandWiki_zero_prefix_of_context (s : Expr)
    (context : YesMetaZFC.BMS.ExpansionContext (encode s)) :
    (expandWiki s 0).take context.lastIndex = s.take context.lastIndex := by
  apply Expr.ext
  change (expandWiki s 0).values.take context.lastIndex = s.values.take context.lastIndex
  rw [expandWiki_zero_values_of_context s context, List.take_append_of_le_length]
  · exact List.take_take.trans (congrArg (fun count => s.values.take count) (Nat.min_self _))
  · have hLength : s.values.length = context.lastIndex + 1 := by
      simpa only [encode_length] using context.array_length
    simp [List.length_take]
    omega

theorem expandWiki_zero_last_of_context (s : Expr)
    (context : YesMetaZFC.BMS.ExpansionContext (encode s)) :
    (expandWiki s 0).values[context.lastIndex]?.getD 0 =
      s.values[context.lastIndex]?.getD 0 - 1 := by
  have hLength : s.values.length = context.lastIndex + 1 := by
    simpa only [encode_length] using context.array_length
  have hTakeLength : (s.values.take context.lastIndex).length = context.lastIndex := by
    simp [List.length_take, Nat.min_eq_left (by omega : context.lastIndex ≤ s.values.length)]
  rw [expandWiki_zero_values_of_context s context, List.getElem?_append_right (by omega),
    hTakeLength, Nat.sub_self]
  rfl

/-- 非空输入的完整 q=1 数值公式：末项为 1 则删去，否则减去 1。 -/
theorem expandWiki_zero_values (s : Expr) (hNonempty : s.values ≠ []) :
    (expandWiki s 0).values =
      if s.values[s.values.length - 1]?.getD 0 = 1 then s.values.take (s.values.length - 1)
      else s.values.take (s.values.length - 1) ++ [s.values[s.values.length - 1]?.getD 0 - 1] := by
  by_cases hOne : s.values[s.values.length - 1]?.getD 0 = 1
  · rw [if_pos hOne, expandWiki_eq_take_of_no_site s 0
      ((expansionSite_none_iff_last_one s hNonempty).mpr hOne)]
    rfl
  · rw [if_neg hOne]
    cases hMaximal : YesMetaZFC.BMS.maximalParentRow (encode s).raw with
    | none =>
        have hSite := (expansionSite_none_iff s).mpr hMaximal
        exact False.elim (hOne ((expansionSite_none_iff_last_one s hNonempty).mp hSite))
    | some row =>
        obtain ⟨context⟩ := YesMetaZFC.BMS.exists_expansionContext_of_maximalParentRow_eq_some hMaximal
        have hLength : s.values.length = context.lastIndex + 1 := by
          simpa only [encode_length] using context.array_length
        simpa only [hLength, Nat.add_sub_cancel] using expandWiki_zero_values_of_context s context

/-- 反复使用 q=1 即可删除最后一项；这不依赖任何良基性定理。 -/
theorem wikiPath_delete (s : Expr) : WikiExpansionPath s (s.take (s.values.length - 1)) := by
  have hMeasure : ∀ value, ∀ current : Expr,
      current.values[current.values.length - 1]?.getD 0 = value →
        WikiExpansionPath current (current.take (current.values.length - 1)) := by
    intro value
    induction value using Nat.strongRecOn with
    | ind value ih =>
        intro current hValue
        cases hMaximal : YesMetaZFC.BMS.maximalParentRow (encode current).raw with
        | none =>
            have hNone := (expansionSite_none_iff current).mpr hMaximal
            rw [← expandWiki_eq_take_of_no_site current 0 hNone]
            exact WikiExpansionPath.single current 0
        | some row =>
            obtain ⟨context⟩ :=
              YesMetaZFC.BMS.exists_expansionContext_of_maximalParentRow_eq_some hMaximal
            have hLength : current.values.length = context.lastIndex + 1 := by
              simpa only [encode_length] using context.array_length
            let shorter := expandWiki current 0
            have hShorterLength : shorter.values.length = current.values.length :=
              expandWiki_zero_length_of_context current context
            have hShorterValue : shorter.values[shorter.values.length - 1]?.getD 0 = value - 1 := by
              rw [hShorterLength, hLength, Nat.add_sub_cancel]
              rw [expandWiki_zero_last_of_context current context]
              rw [hLength, Nat.add_sub_cancel] at hValue
              rw [hValue]
            have hPositive : 0 < value - 1 := by
              have hValid : shorter.values.length - 1 < shorter.values.length := by omega
              have hp := positive_getD (layer := ⟨shorter.values, linearParent⟩) shorter.legal.1 hValid
              rwa [hShorterValue] at hp
            have hNext := ih (value - 1) (by omega) shorter hShorterValue
            have hTarget : shorter.take (shorter.values.length - 1) =
                current.take (current.values.length - 1) := by
              rw [hShorterLength, hLength, Nat.add_sub_cancel]
              exact expandWiki_zero_prefix_of_context current context
            rw [hTarget] at hNext
            exact (WikiExpansionPath.single current 0).trans hNext
  exact hMeasure _ s rfl

theorem wikiPath_take (s : Expr) (count : Nat) : WikiExpansionPath s (s.take count) :=
  prefix_reachable_of_delete WikiExpansionPath WikiExpansionPath.refl
    (fun hLeft hRight => WikiExpansionPath.trans hLeft hRight) wikiPath_delete s count

theorem wikiGenerated_take {s : Expr} (hGenerated : WikiGenerated s) (count : Nat) :
    WikiGenerated (s.take count) := wikiGenerated_of_path hGenerated (wikiPath_take s count)

theorem wikiPath_expandY (s : Expr) (index : Nat) : WikiExpansionPath s (expandY s index) := by
  rw [← expandY_eq_wiki_take s index]
  exact (WikiExpansionPath.single s index).trans (wikiPath_take _ _)

/-- 两种端点约定生成完全相同的标准表达式集合。 -/
theorem wikiGenerated_iff_yGenerated (s : Expr) : WikiGenerated s ↔ YGenerated s := by
  constructor
  · intro hGenerated
    induction hGenerated with
    | seed height => exact .seed height
    | expand prior index ih => exact yGenerated_of_path ih (yExpansionPath_expandWiki _ index)
  · intro hGenerated
    induction hGenerated with
    | seed height => exact .seed height
    | expand prior index ih => exact wikiGenerated_of_path ih (wikiPath_expandY _ index)

/-- 实际任意起点的可达闭包也与端点选择无关。 -/
theorem wikiPath_iff_yPath (root target : Expr) :
    WikiExpansionPath root target ↔ YExpansionPath root target := by
  constructor
  · intro hPath
    induction hPath with
    | refl => exact .refl _
    | tail prior index ih => exact ih.trans (yExpansionPath_expandWiki _ index)
  · intro hPath
    induction hPath with
    | refl => exact .refl _
    | tail prior index ih => exact ih.trans (wikiPath_expandY _ index)

/-- 有限完整块路径若端点不同，就给出非空的严格展开路径。 -/
theorem yPath_eq_or_transGen {root target : Expr} (hPath : YExpansionPath root target) :
    target = root ∨ Relation.TransGen YStep target root := by
  induction hPath with
  | refl => exact Or.inl rfl
  | @tail middle prior index ih =>
      by_cases hEqual : expandY middle index = middle
      · rw [hEqual]
        exact ih
      · have hStep : YStep (expandY middle index) middle := ⟨⟨index, rfl⟩, hEqual⟩
        apply Or.inr
        rcases ih with hRoot | hEarlier
        · rw [← hRoot]
          exact Relation.TransGen.single hStep
        · exact Relation.TransGen.trans (Relation.TransGen.single hStep) hEarlier

/-- Wiki 的非平凡一步在完整块系统中是非空有限展开路径。 -/
theorem wikiStep_transGen_yStep {smaller larger : Expr} (hStep : WikiStep smaller larger) :
    Relation.TransGen YStep smaller larger := by
  obtain ⟨⟨index, hExpanded⟩, hDifferent⟩ := hStep
  have hPath := yExpansionPath_expandWiki larger index
  rw [hExpanded] at hPath
  rcases yPath_eq_or_transGen hPath with hEqual | hStrict
  · exact False.elim (hDifferent hEqual)
  · exact hStrict

end ZeroY
