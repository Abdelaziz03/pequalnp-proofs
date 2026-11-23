import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1001

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.and, [2, 13]⟩,
    ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.and, [3, 15]⟩,
    ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.and, [6, 17]⟩,
    ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [5, 19]⟩,
    ⟨GateOp.or, [11, 14]⟩, ⟨GateOp.or, [21, 16]⟩, ⟨GateOp.or, [22, 18]⟩,
    ⟨GateOp.or, [23, 20]⟩], 24⟩

lemma fanin : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma eval_all : ∀ a b c d e f g h i : Bool,
    circuit.eval [a, b, c, d, e, f, g, h, i] = ((a && b) || (b && c) || (c && d) || (d && e) || (e && a) || (a && f) || (b && g) || (c && h) || (d && i) || (f && h) || (g && i) || (i && f)) := by
  intro a b c d e f g h i
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;>
    cases h <;> cases i <;> rfl

lemma main : PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 16 := by
  refine ⟨circuit, fanin, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact eval_all (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)

end PEqualNP.Outside.L_meta_1001

theorem PEqualNP.Outside.L_meta_1001 : PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 16 :=
  PEqualNP.Outside.L_meta_1001.main
