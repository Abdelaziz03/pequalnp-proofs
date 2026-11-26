import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20440 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16269874 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 16] }], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
