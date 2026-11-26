import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19566 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24894758 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 16] }], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
