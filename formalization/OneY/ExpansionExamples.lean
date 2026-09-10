import OneY.ExpansionCompute

/-! # Kernel-checked outputs of the concrete 1-Y expansion -/

namespace OneY.Numeric.ExpansionExamples

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

theorem legal_two : ZeroY.Legal [1, 2] := by simp [ZeroY.Legal]
theorem legal_three : ZeroY.Legal [1, 3] := by simp [ZeroY.Legal]
theorem legal_parentless : ZeroY.Legal [1, 3, 1] := by simp [ZeroY.Legal]
theorem legal_ordinary : ZeroY.Legal [1, 3, 2] := by simp [ZeroY.Legal]
theorem legal_repeated : ZeroY.Legal [1, 3, 3] := by simp [ZeroY.Legal]

theorem two : expandValues [1, 2] legal_two 3 = [1, 1, 1, 1] := by
  rw [expandValues_eq_compute]
  decide

theorem three : expandValues [1, 3] legal_three 3 = [1, 2, 4, 8] := by
  rw [expandValues_eq_compute]
  decide_cbv

theorem parentless : expandValues [1, 3, 1] legal_parentless 3 = [1, 3] := by
  decide

theorem ordinary : expandValues [1, 3, 2] legal_ordinary 3 =
    [1, 3, 1, 3, 1, 3, 1, 3] := by
  rw [expandValues_eq_compute]
  decide

theorem repeated_badRoot : findBadRoot [1, 3, 3] legal_repeated 2 =
    some ⟨1, 0, 0⟩ := by decide_cbv

theorem repeated : expandValues [1, 3, 3] legal_repeated 1 = [1, 3, 2, 5] := by
  rw [expandValues_eq_compute]
  decide_cbv

theorem legal_repeated_output : ZeroY.Legal [1, 3, 2, 5] := by simp [ZeroY.Legal]

/-- The extracted layer copies correctly. Its values sit at the varying
column tops, not at a single fixed physical row. -/
theorem repeated_output_extracted :
    (List.range 4).map (layers (rootedSequence [1, 3, 2, 5] legal_repeated_output) 1).row.value =
      [1, 2, 1, 2] := by decide_cbv

theorem repeated_output_heights :
    (List.range 4).map (height (ofSequence [1, 3, 2, 5])) = [0, 1, 1, 2] := by
  decide_cbv

theorem repeated_output_lifted_top : (rows (ofSequence [1, 3, 2, 5]) 2).value 3 = 2 := by
  decide_cbv

theorem repeated_output_reference_cell : (rows (ofSequence [1, 3, 2, 5]) 1).value 3 = 3 := by
  decide_cbv

end OneY.Numeric.ExpansionExamples

#print axioms OneY.Numeric.ExpansionExamples.two
#print axioms OneY.Numeric.ExpansionExamples.three
#print axioms OneY.Numeric.ExpansionExamples.repeated
#print axioms OneY.Numeric.ExpansionExamples.repeated_output_extracted
