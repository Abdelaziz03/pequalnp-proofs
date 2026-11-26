import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19156

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- NOT (x_i OR y_j): two gates. -/
def circ (n : ℕ) (i j : Fin n) : Circuit :=
  ⟨[⟨GateOp.or, [i.val, n + j.val]⟩, ⟨GateOp.not, [n + n]⟩], n + n + 1⟩

theorem len (n : ℕ) (u v : Fin n) : (oneEach u v).length = n + n := by
  simp [oneEach]

theorem rowWire (n : ℕ) (i u v : Fin n) : (oneEach u v).getD i.val false = decide (i = u) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
  simp

theorem colWire (n : ℕ) (j u v : Fin n) : (oneEach u v).getD (n + j.val) false = decide (j = v) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem eval_eq (n : ℕ) (i j u v : Fin n) :
    (circ n i j).eval (oneEach u v) = (decide (u ≠ i) && decide (v ≠ j)) := by
  have h1 := rowWire n i u v
  have h2 := colWire n j u v
  have hl := len n u v
  simp only [circ, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, GateOp.eval,
    List.map_cons, List.map_nil, h1, h2]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
  simp only [hl]
  by_cases a : i = u <;> by_cases b : j = v <;> simp [a, b, eq_comm]

theorem fan (n : ℕ) (i j : Fin n) : FanInTwo (circ n i j) := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19156

theorem PEqualNP.Outside.L_meta_19156 : ∀ (n : ℕ) (i j : Fin n), ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j)) C := by
  intro n i j
  exact ⟨PEqualNP.Outside.L_meta_19156.circ n i j, PEqualNP.Outside.L_meta_19156.fan n i j, by simp [PEqualNP.Outside.L_meta_19156.circ, PEqualNP.CircuitLowerBounds.Circuit.size],
    fun u v => PEqualNP.Outside.L_meta_19156.eval_eq n i j u v⟩
