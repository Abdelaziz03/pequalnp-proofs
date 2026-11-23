import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def c0 : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩], 2⟩

lemma fan0 : FanInTwo c0 := by
  intro g hg
  simp only [c0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h <;> subst g <;> simp

lemma ev0 : ∀ a b : Bool, c0.eval [a, b] = ((a && b)) := by
  decide +kernel

lemma h0 : PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1 := by
  refine ⟨c0, fan0, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev0 (x 0) (x 1)

def c1 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩], 4⟩

lemma fan1 : FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h <;> subst g <;> simp

lemma ev1 : ∀ a b c : Bool, c1.eval [a, b, c] = ((a && b) || (a && c)) := by
  decide +kernel

lemma h1 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2 := by
  refine ⟨c1, fan1, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev1 (x 0) (x 1) (x 2)

def c2 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩

lemma fan2 : FanInTwo c2 := by
  intro g hg
  simp only [c2, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h <;> subst g <;> simp

lemma ev2 : ∀ a b c : Bool, c2.eval [a, b, c] = ((a && b) || (a && c) || (b && c)) := by
  decide +kernel

lemma h2 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 := by
  refine ⟨c2, fan2, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev2 (x 0) (x 1) (x 2)

def c3 : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩

lemma fan3 : FanInTwo c3 := by
  intro g hg
  simp only [c3, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h <;> subst g <;> simp

lemma ev3 : ∀ a b c d : Bool, c3.eval [a, b, c, d] = ((a && b) || (c && d)) := by
  decide +kernel

lemma h3 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 := by
  refine ⟨c3, fan3, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev3 (x 0) (x 1) (x 2) (x 3)

def c4 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.and, [0, 5]⟩], 6⟩

lemma fan4 : FanInTwo c4 := by
  intro g hg
  simp only [c4, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h <;> subst g <;> simp

lemma ev4 : ∀ a b c d : Bool, c4.eval [a, b, c, d] = ((a && b) || (a && c) || (a && d)) := by
  decide +kernel

lemma h4 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3 := by
  refine ⟨c4, fan4, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev4 (x 0) (x 1) (x 2) (x 3)

def c5 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [5, 6]⟩], 7⟩

lemma fan5 : FanInTwo c5 := by
  intro g hg
  simp only [c5, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h <;> subst g <;> simp

lemma ev5 : ∀ a b c d : Bool, c5.eval [a, b, c, d] = ((a && b) || (a && c) || (b && d)) := by
  decide +kernel

lemma h5 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4 := by
  refine ⟨c5, fan5, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev5 (x 0) (x 1) (x 2) (x 3)

def c6 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [6, 7]⟩], 8⟩

lemma fan6 : FanInTwo c6 := by
  intro g hg
  simp only [c6, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h <;> subst g <;> simp

lemma ev6 : ∀ a b c d : Bool, c6.eval [a, b, c, d] = ((a && b) || (a && c) || (a && d) || (b && c)) := by
  decide +kernel

lemma h6 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5 := by
  refine ⟨c6, fan6, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev6 (x 0) (x 1) (x 2) (x 3)

def c7 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [6, 7]⟩], 8⟩

lemma fan7 : FanInTwo c7 := by
  intro g hg
  simp only [c7, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h <;> subst g <;> simp

lemma ev7 : ∀ a b c d e : Bool, c7.eval [a, b, c, d, e] = ((a && b) || (a && c) || (d && e)) := by
  decide +kernel

lemma h7 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4 := by
  refine ⟨c7, fan7, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev7 (x 0) (x 1) (x 2) (x 3) (x 4)

def c8 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [0, 7]⟩], 8⟩

lemma fan8 : FanInTwo c8 := by
  intro g hg
  simp only [c8, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h <;> subst g <;> simp

lemma ev8 : ∀ a b c d e : Bool, c8.eval [a, b, c, d, e] = ((a && b) || (a && c) || (a && d) || (a && e)) := by
  decide +kernel

lemma h8 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 := by
  refine ⟨c8, fan8, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev8 (x 0) (x 1) (x 2) (x 3) (x 4)

def c9 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [7, 8]⟩], 9⟩

lemma fan9 : FanInTwo c9 := by
  intro g hg
  simp only [c9, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h <;> subst g <;> simp

lemma ev9 : ∀ a b c d e : Bool, c9.eval [a, b, c, d, e] = ((a && b) || (a && c) || (a && d) || (b && e)) := by
  decide +kernel

lemma h9 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5 := by
  refine ⟨c9, fan9, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev9 (x 0) (x 1) (x 2) (x 3) (x 4)

def c10 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [9, 8]⟩], 10⟩

lemma fan10 : FanInTwo c10 := by
  intro g hg
  simp only [c10, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst g <;> simp

lemma ev10 : ∀ a b c d e : Bool, c10.eval [a, b, c, d, e] = ((a && b) || (a && c) || (b && c) || (d && e)) := by
  decide +kernel

lemma h10 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6 := by
  refine ⟨c10, fan10, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev10 (x 0) (x 1) (x 2) (x 3) (x 4)

def c11 : Circuit := ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [6, 8]⟩], 9⟩

lemma fan11 : FanInTwo c11 := by
  intro g hg
  simp only [c11, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h <;> subst g <;> simp

lemma ev11 : ∀ a b c d e : Bool, c11.eval [a, b, c, d, e] = ((a && b) || (a && c) || (b && d) || (c && e)) := by
  decide +kernel

lemma h11 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5 := by
  refine ⟨c11, fan11, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev11 (x 0) (x 1) (x 2) (x 3) (x 4)

def c12 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩

lemma fan12 : FanInTwo c12 := by
  intro g hg
  simp only [c12, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst g <;> simp

lemma ev12 : ∀ a b c d e : Bool, c12.eval [a, b, c, d, e] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c)) := by
  decide +kernel

lemma h12 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6 := by
  refine ⟨c12, fan12, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev12 (x 0) (x 1) (x 2) (x 3) (x 4)

def c13 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [7, 9]⟩], 10⟩

lemma fan13 : FanInTwo c13 := by
  intro g hg
  simp only [c13, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst g <;> simp

lemma ev13 : ∀ a b c d e : Bool, c13.eval [a, b, c, d, e] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e)) := by
  decide +kernel

lemma h13 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6 := by
  refine ⟨c13, fan13, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev13 (x 0) (x 1) (x 2) (x 3) (x 4)

def c14 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [10, 9]⟩], 11⟩

lemma fan14 : FanInTwo c14 := by
  intro g hg
  simp only [c14, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev14 : ∀ a b c d e : Bool, c14.eval [a, b, c, d, e] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e)) := by
  decide +kernel

lemma h14 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7 := by
  refine ⟨c14, fan14, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev14 (x 0) (x 1) (x 2) (x 3) (x 4)

def c15 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [10, 9]⟩], 11⟩

lemma fan15 : FanInTwo c15 := by
  intro g hg
  simp only [c15, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev15 : ∀ a b c d e : Bool, c15.eval [a, b, c, d, e] = ((a && b) || (a && c) || (b && d) || (c && e) || (d && e)) := by
  decide +kernel

lemma h15 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7 := by
  refine ⟨c15, fan15, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev15 (x 0) (x 1) (x 2) (x 3) (x 4)

def c16 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

lemma fan16 : FanInTwo c16 := by
  intro g hg
  simp only [c16, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev16 : ∀ a b c d e : Bool, c16.eval [a, b, c, d, e] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && e)) := by
  decide +kernel

lemma h16 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8 := by
  refine ⟨c16, fan16, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev16 (x 0) (x 1) (x 2) (x 3) (x 4)

def c17 : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [9, 8]⟩], 10⟩

lemma fan17 : FanInTwo c17 := by
  intro g hg
  simp only [c17, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h <;> subst g <;> simp

lemma ev17 : ∀ a b c d e f : Bool, c17.eval [a, b, c, d, e, f] = ((a && b) || (c && d) || (e && f)) := by
  decide +kernel

lemma h17 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨c17, fan17, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev17 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c18 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩

lemma fan18 : FanInTwo c18 := by
  intro g hg
  simp only [c18, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h <;> subst g <;> simp

lemma ev18 : ∀ a b c d e f : Bool, c18.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (e && f)) := by
  decide +kernel

lemma h18 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨c18, fan18, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev18 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c19 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [10, 9]⟩], 11⟩

lemma fan19 : FanInTwo c19 := by
  intro g hg
  simp only [c19, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst g <;> simp

lemma ev19 : ∀ a b c d e f : Bool, c19.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (b && d) || (e && f)) := by
  decide +kernel

lemma h19 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6 := by
  refine ⟨c19, fan19, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev19 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c20 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.or, [7, 9]⟩], 10⟩

lemma fan20 : FanInTwo c20 := by
  intro g hg
  simp only [c20, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h <;> subst g <;> simp

lemma ev20 : ∀ a b c d e f : Bool, c20.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (d && e) || (d && f)) := by
  decide +kernel

lemma h20 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5 := by
  refine ⟨c20, fan20, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev20 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c21 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [0, 9]⟩], 10⟩

lemma fan21 : FanInTwo c21 := by
  intro g hg
  simp only [c21, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h <;> subst g <;> simp

lemma ev21 : ∀ a b c d e f : Bool, c21.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f)) := by
  decide +kernel

lemma h21 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5 := by
  refine ⟨c21, fan21, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev21 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c22 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [9, 10]⟩], 11⟩

lemma fan22 : FanInTwo c22 := by
  intro g hg
  simp only [c22, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst g <;> simp

lemma ev22 : ∀ a b c d e f : Bool, c22.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f)) := by
  decide +kernel

lemma h22 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨c22, fan22, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev22 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c23 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

lemma fan23 : FanInTwo c23 := by
  intro g hg
  simp only [c23, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev23 : ∀ a b c d e f : Bool, c23.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && c) || (e && f)) := by
  decide +kernel

lemma h23 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7 := by
  refine ⟨c23, fan23, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev23 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c24 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [8, 10]⟩], 11⟩

lemma fan24 : FanInTwo c24 := by
  intro g hg
  simp only [c24, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst g <;> simp

lemma ev24 : ∀ a b c d e f : Bool, c24.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && e) || (b && f)) := by
  decide +kernel

lemma h24 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨c24, fan24, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev24 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c25 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

lemma fan25 : FanInTwo c25 := by
  intro g hg
  simp only [c25, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev25 : ∀ a b c d e f : Bool, c25.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f)) := by
  decide +kernel

lemma h25 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7 := by
  refine ⟨c25, fan25, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev25 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c26 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [8, 10]⟩], 11⟩

lemma fan26 : FanInTwo c26 := by
  intro g hg
  simp only [c26, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst g <;> simp

lemma ev26 : ∀ a b c d e f : Bool, c26.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && e) || (e && f)) := by
  decide +kernel

lemma h26 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6 := by
  refine ⟨c26, fan26, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev26 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c27 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

lemma fan27 : FanInTwo c27 := by
  intro g hg
  simp only [c27, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev27 : ∀ a b c d e f : Bool, c27.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (b && c) || (d && e) || (d && f)) := by
  decide +kernel

lemma h27 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨c27, fan27, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev27 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c28 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

lemma fan28 : FanInTwo c28 := by
  intro g hg
  simp only [c28, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev28 : ∀ a b c d e f : Bool, c28.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (b && d) || (c && e) || (d && f)) := by
  decide +kernel

lemma h28 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨c28, fan28, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev28 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c29 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [10, 11]⟩], 12⟩

lemma fan29 : FanInTwo c29 := by
  intro g hg
  simp only [c29, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev29 : ∀ a b c d e f : Bool, c29.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c)) := by
  decide +kernel

lemma h29 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7 := by
  refine ⟨c29, fan29, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev29 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c30 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12⟩

lemma fan30 : FanInTwo c30 := by
  intro g hg
  simp only [c30, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev30 : ∀ a b c d e f : Bool, c30.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f)) := by
  decide +kernel

lemma h30 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7 := by
  refine ⟨c30, fan30, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev30 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c31 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

lemma fan31 : FanInTwo c31 := by
  intro g hg
  simp only [c31, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev31 : ∀ a b c d e f : Bool, c31.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && f)) := by
  decide +kernel

lemma h31 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8 := by
  refine ⟨c31, fan31, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev31 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c32 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

lemma fan32 : FanInTwo c32 := by
  intro g hg
  simp only [c32, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev32 : ∀ a b c d e f : Bool, c32.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (c && f)) := by
  decide +kernel

lemma h32 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8 := by
  refine ⟨c32, fan32, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev32 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c33 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

lemma fan33 : FanInTwo c33 := by
  intro g hg
  simp only [c33, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev33 : ∀ a b c d e f : Bool, c33.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f)) := by
  decide +kernel

lemma h33 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨c33, fan33, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev33 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c34 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

lemma fan34 : FanInTwo c34 := by
  intro g hg
  simp only [c34, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev34 : ∀ a b c d e f : Bool, c34.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (d && f)) := by
  decide +kernel

lemma h34 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨c34, fan34, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev34 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c35 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

lemma fan35 : FanInTwo c35 := by
  intro g hg
  simp only [c35, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev35 : ∀ a b c d e f : Bool, c35.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (e && f)) := by
  decide +kernel

lemma h35 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8 := by
  refine ⟨c35, fan35, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev35 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c36 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

lemma fan36 : FanInTwo c36 := by
  intro g hg
  simp only [c36, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev36 : ∀ a b c d e f : Bool, c36.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (e && f)) := by
  decide +kernel

lemma h36 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨c36, fan36, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev36 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c37 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.or, [13, 11]⟩], 14⟩

lemma fan37 : FanInTwo c37 := by
  intro g hg
  simp only [c37, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev37 : ∀ a b c d e f : Bool, c37.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (b && c) || (d && e) || (d && f) || (e && f)) := by
  decide +kernel

lemma h37 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨c37, fan37, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev37 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c38 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

lemma fan38 : FanInTwo c38 := by
  intro g hg
  simp only [c38, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev38 : ∀ a b c d e f : Bool, c38.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (b && d) || (c && e) || (d && f) || (e && f)) := by
  decide +kernel

lemma h38 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨c38, fan38, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev38 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c39 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma fan39 : FanInTwo c39 := by
  intro g hg
  simp only [c39, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev39 : ∀ a b c d e f : Bool, c39.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c) || (d && e)) := by
  decide +kernel

lemma h39 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9 := by
  refine ⟨c39, fan39, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev39 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c40 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma fan40 : FanInTwo c40 := by
  intro g hg
  simp only [c40, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev40 : ∀ a b c d e f : Bool, c40.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (d && e)) := by
  decide +kernel

lemma h40 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9 := by
  refine ⟨c40, fan40, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev40 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c41 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma fan41 : FanInTwo c41 := by
  intro g hg
  simp only [c41, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev41 : ∀ a b c d e f : Bool, c41.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (e && f)) := by
  decide +kernel

lemma h41 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨c41, fan41, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev41 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c42 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

lemma fan42 : FanInTwo c42 := by
  intro g hg
  simp only [c42, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst g <;> simp

lemma ev42 : ∀ a b c d e f g : Bool, c42.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (d && e) || (f && g)) := by
  decide +kernel

lemma h42 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨c42, fan42, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev42 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c43 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 11]⟩], 12⟩

lemma fan43 : FanInTwo c43 := by
  intro g hg
  simp only [c43, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst g <;> simp

lemma ev43 : ∀ a b c d e f g : Bool, c43.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (f && g)) := by
  decide +kernel

lemma h43 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨c43, fan43, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev43 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c44 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

lemma fan44 : FanInTwo c44 := by
  intro g hg
  simp only [c44, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev44 : ∀ a b c d e f g : Bool, c44.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (f && g)) := by
  decide +kernel

lemma h44 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨c44, fan44, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev44 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c45 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12⟩

lemma fan45 : FanInTwo c45 := by
  intro g hg
  simp only [c45, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst g <;> simp

lemma ev45 : ∀ a b c d e f g : Bool, c45.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (e && f) || (e && g)) := by
  decide +kernel

lemma h45 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6 := by
  refine ⟨c45, fan45, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev45 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c46 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.or, [13, 11]⟩], 14⟩

lemma fan46 : FanInTwo c46 := by
  intro g hg
  simp only [c46, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev46 : ∀ a b c d e f g : Bool, c46.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (b && c) || (d && e) || (f && g)) := by
  decide +kernel

lemma h46 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨c46, fan46, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev46 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c47 : Circuit := ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

lemma fan47 : FanInTwo c47 := by
  intro g hg
  simp only [c47, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev47 : ∀ a b c d e f g : Bool, c47.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (b && d) || (c && e) || (f && g)) := by
  decide +kernel

lemma h47 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨c47, fan47, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev47 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c48 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

lemma fan48 : FanInTwo c48 := by
  intro g hg
  simp only [c48, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev48 : ∀ a b c d e f g : Bool, c48.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (b && d) || (e && f) || (e && g)) := by
  decide +kernel

lemma h48 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨c48, fan48, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev48 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c49 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩], 12⟩

lemma fan49 : FanInTwo c49 := by
  intro g hg
  simp only [c49, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst g <;> simp

lemma ev49 : ∀ a b c d e f g : Bool, c49.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (a && g)) := by
  decide +kernel

lemma h49 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6 := by
  refine ⟨c49, fan49, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev49 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c50 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩

lemma fan50 : FanInTwo c50 := by
  intro g hg
  simp only [c50, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev50 : ∀ a b c d e f g : Bool, c50.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && g)) := by
  decide +kernel

lemma h50 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨c50, fan50, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev50 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c51 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma fan51 : FanInTwo c51 := by
  intro g hg
  simp only [c51, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev51 : ∀ a b c d e f g : Bool, c51.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (f && g)) := by
  decide +kernel

lemma h51 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8 := by
  refine ⟨c51, fan51, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev51 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c52 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [10, 12]⟩], 13⟩

lemma fan52 : FanInTwo c52 := by
  intro g hg
  simp only [c52, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev52 : ∀ a b c d e f g : Bool, c52.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (b && g)) := by
  decide +kernel

lemma h52 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨c52, fan52, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev52 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c53 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma fan53 : FanInTwo c53 := by
  intro g hg
  simp only [c53, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev53 : ∀ a b c d e f g : Bool, c53.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (c && g)) := by
  decide +kernel

lemma h53 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨c53, fan53, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev53 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c54 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [10, 12]⟩], 13⟩

lemma fan54 : FanInTwo c54 := by
  intro g hg
  simp only [c54, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev54 : ∀ a b c d e f g : Bool, c54.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (f && g)) := by
  decide +kernel

lemma h54 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7 := by
  refine ⟨c54, fan54, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev54 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c55 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma fan55 : FanInTwo c55 := by
  intro g hg
  simp only [c55, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev55 : ∀ a b c d e f g : Bool, c55.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (f && g)) := by
  decide +kernel

lemma h55 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨c55, fan55, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev55 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c56 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩

lemma fan56 : FanInTwo c56 := by
  intro g hg
  simp only [c56, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev56 : ∀ a b c d e f g : Bool, c56.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (f && g)) := by
  decide +kernel

lemma h56 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨c56, fan56, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev56 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c57 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma fan57 : FanInTwo c57 := by
  intro g hg
  simp only [c57, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev57 : ∀ a b c d e f g : Bool, c57.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (e && f) || (e && g)) := by
  decide +kernel

lemma h57 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨c57, fan57, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev57 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c58 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma fan58 : FanInTwo c58 := by
  intro g hg
  simp only [c58, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev58 : ∀ a b c d e f g : Bool, c58.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (b && f) || (c && g)) := by
  decide +kernel

lemma h58 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨c58, fan58, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev58 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c59 : Circuit := ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma fan59 : FanInTwo c59 := by
  intro g hg
  simp only [c59, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev59 : ∀ a b c d e f g : Bool, c59.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (d && g)) := by
  decide +kernel

lemma h59 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8 := by
  refine ⟨c59, fan59, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev59 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c60 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma fan60 : FanInTwo c60 := by
  intro g hg
  simp only [c60, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev60 : ∀ a b c d e f g : Bool, c60.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (e && g)) := by
  decide +kernel

lemma h60 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨c60, fan60, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev60 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c61 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [9, 12]⟩], 13⟩

lemma fan61 : FanInTwo c61 := by
  intro g hg
  simp only [c61, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev61 : ∀ a b c d e f g : Bool, c61.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (e && f) || (e && g)) := by
  decide +kernel

lemma h61 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨c61, fan61, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev61 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c62 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma fan62 : FanInTwo c62 := by
  intro g hg
  simp only [c62, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev62 : ∀ a b c d e f g : Bool, c62.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (e && f) || (f && g)) := by
  decide +kernel

lemma h62 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8 := by
  refine ⟨c62, fan62, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev62 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c63 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma fan63 : FanInTwo c63 := by
  intro g hg
  simp only [c63, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev63 : ∀ a b c d e f g : Bool, c63.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (e && f) || (e && g) || (f && g)) := by
  decide +kernel

lemma h63 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8 := by
  refine ⟨c63, fan63, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev63 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c64 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩

lemma fan64 : FanInTwo c64 := by
  intro g hg
  simp only [c64, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev64 : ∀ a b c d e f g : Bool, c64.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (b && c) || (d && e) || (d && f) || (e && g)) := by
  decide +kernel

lemma h64 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨c64, fan64, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev64 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c65 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩

lemma fan65 : FanInTwo c65 := by
  intro g hg
  simp only [c65, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev65 : ∀ a b c d e f g : Bool, c65.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (b && d) || (c && e) || (d && e) || (f && g)) := by
  decide +kernel

lemma h65 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨c65, fan65, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev65 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c66 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma fan66 : FanInTwo c66 := by
  intro g hg
  simp only [c66, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev66 : ∀ a b c d e f g : Bool, c66.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (b && d) || (c && e) || (d && f) || (e && g)) := by
  decide +kernel

lemma h66 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨c66, fan66, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev66 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c67 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩

lemma fan67 : FanInTwo c67 := by
  intro g hg
  simp only [c67, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev67 : ∀ a b c d e f g : Bool, c67.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (a && g) || (b && c)) := by
  decide +kernel

lemma h67 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8 := by
  refine ⟨c67, fan67, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev67 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c68 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩

lemma fan68 : FanInTwo c68 := by
  intro g hg
  simp only [c68, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev68 : ∀ a b c d e f g : Bool, c68.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c) || (b && g)) := by
  decide +kernel

lemma h68 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8 := by
  refine ⟨c68, fan68, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev68 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c69 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan69 : FanInTwo c69 := by
  intro g hg
  simp only [c69, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev69 : ∀ a b c d e f g : Bool, c69.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c) || (d && g)) := by
  decide +kernel

lemma h69 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9 := by
  refine ⟨c69, fan69, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev69 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c70 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [10, 13]⟩], 14⟩

lemma fan70 : FanInTwo c70 := by
  intro g hg
  simp only [c70, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev70 : ∀ a b c d e f g : Bool, c70.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (b && g)) := by
  decide +kernel

lemma h70 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8 := by
  refine ⟨c70, fan70, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev70 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c71 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan71 : FanInTwo c71 := by
  intro g hg
  simp only [c71, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev71 : ∀ a b c d e f g : Bool, c71.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (c && g)) := by
  decide +kernel

lemma h71 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9 := by
  refine ⟨c71, fan71, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev71 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c72 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan72 : FanInTwo c72 := by
  intro g hg
  simp only [c72, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev72 : ∀ a b c d e f g : Bool, c72.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (d && g)) := by
  decide +kernel

lemma h72 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨c72, fan72, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev72 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c73 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan73 : FanInTwo c73 := by
  intro g hg
  simp only [c73, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev73 : ∀ a b c d e f g : Bool, c73.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (f && g)) := by
  decide +kernel

lemma h73 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨c73, fan73, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev73 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c74 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan74 : FanInTwo c74 := by
  intro g hg
  simp only [c74, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev74 : ∀ a b c d e f g : Bool, c74.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && f) || (d && g)) := by
  decide +kernel

lemma h74 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨c74, fan74, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev74 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c75 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan75 : FanInTwo c75 := by
  intro g hg
  simp only [c75, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev75 : ∀ a b c d e f g : Bool, c75.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && f) || (f && g)) := by
  decide +kernel

lemma h75 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨c75, fan75, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev75 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c76 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan76 : FanInTwo c76 := by
  intro g hg
  simp only [c76, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev76 : ∀ a b c d e f g : Bool, c76.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (b && g) || (f && g)) := by
  decide +kernel

lemma h76 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨c76, fan76, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev76 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c77 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan77 : FanInTwo c77 := by
  intro g hg
  simp only [c77, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev77 : ∀ a b c d e f g : Bool, c77.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (c && g) || (f && g)) := by
  decide +kernel

lemma h77 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨c77, fan77, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev77 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c78 : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan78 : FanInTwo c78 := by
  intro g hg
  simp only [c78, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev78 : ∀ a b c d e f g : Bool, c78.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (c && f) || (d && g)) := by
  decide +kernel

lemma h78 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨c78, fan78, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev78 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c79 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan79 : FanInTwo c79 := by
  intro g hg
  simp only [c79, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev79 : ∀ a b c d e f g : Bool, c79.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (d && g)) := by
  decide +kernel

lemma h79 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨c79, fan79, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev79 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c80 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan80 : FanInTwo c80 := by
  intro g hg
  simp only [c80, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev80 : ∀ a b c d e f g : Bool, c80.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (f && g)) := by
  decide +kernel

lemma h80 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨c80, fan80, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev80 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c81 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan81 : FanInTwo c81 := by
  intro g hg
  simp only [c81, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev81 : ∀ a b c d e f g : Bool, c81.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (e && f) || (e && g)) := by
  decide +kernel

lemma h81 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨c81, fan81, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev81 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c82 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan82 : FanInTwo c82 := by
  intro g hg
  simp only [c82, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev82 : ∀ a b c d e f g : Bool, c82.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (b && f) || (c && g) || (e && g)) := by
  decide +kernel

lemma h82 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9 := by
  refine ⟨c82, fan82, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev82 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c83 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan83 : FanInTwo c83 := by
  intro g hg
  simp only [c83, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev83 : ∀ a b c d e f g : Bool, c83.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (e && f) || (e && g)) := by
  decide +kernel

lemma h83 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨c83, fan83, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev83 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c84 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma fan84 : FanInTwo c84 := by
  intro g hg
  simp only [c84, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

lemma ev84 : ∀ a b c d e f g : Bool, c84.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (e && g) || (f && g)) := by
  decide +kernel

lemma h84 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨c84, fan84, by decide, ?_⟩
  intro x
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact ev84 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

end PEqualNP.Outside.L_meta_926

theorem PEqualNP.Outside.L_meta_926 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) :=
  ⟨PEqualNP.Outside.L_meta_926.h0, PEqualNP.Outside.L_meta_926.h1, PEqualNP.Outside.L_meta_926.h2, PEqualNP.Outside.L_meta_926.h3, PEqualNP.Outside.L_meta_926.h4, PEqualNP.Outside.L_meta_926.h5, PEqualNP.Outside.L_meta_926.h6, PEqualNP.Outside.L_meta_926.h7, PEqualNP.Outside.L_meta_926.h8, PEqualNP.Outside.L_meta_926.h9, PEqualNP.Outside.L_meta_926.h10, PEqualNP.Outside.L_meta_926.h11, PEqualNP.Outside.L_meta_926.h12, PEqualNP.Outside.L_meta_926.h13, PEqualNP.Outside.L_meta_926.h14, PEqualNP.Outside.L_meta_926.h15, PEqualNP.Outside.L_meta_926.h16, PEqualNP.Outside.L_meta_926.h17, PEqualNP.Outside.L_meta_926.h18, PEqualNP.Outside.L_meta_926.h19, PEqualNP.Outside.L_meta_926.h20, PEqualNP.Outside.L_meta_926.h21, PEqualNP.Outside.L_meta_926.h22, PEqualNP.Outside.L_meta_926.h23, PEqualNP.Outside.L_meta_926.h24, PEqualNP.Outside.L_meta_926.h25, PEqualNP.Outside.L_meta_926.h26, PEqualNP.Outside.L_meta_926.h27, PEqualNP.Outside.L_meta_926.h28, PEqualNP.Outside.L_meta_926.h29, PEqualNP.Outside.L_meta_926.h30, PEqualNP.Outside.L_meta_926.h31, PEqualNP.Outside.L_meta_926.h32, PEqualNP.Outside.L_meta_926.h33, PEqualNP.Outside.L_meta_926.h34, PEqualNP.Outside.L_meta_926.h35, PEqualNP.Outside.L_meta_926.h36, PEqualNP.Outside.L_meta_926.h37, PEqualNP.Outside.L_meta_926.h38, PEqualNP.Outside.L_meta_926.h39, PEqualNP.Outside.L_meta_926.h40, PEqualNP.Outside.L_meta_926.h41, PEqualNP.Outside.L_meta_926.h42, PEqualNP.Outside.L_meta_926.h43, PEqualNP.Outside.L_meta_926.h44, PEqualNP.Outside.L_meta_926.h45, PEqualNP.Outside.L_meta_926.h46, PEqualNP.Outside.L_meta_926.h47, PEqualNP.Outside.L_meta_926.h48, PEqualNP.Outside.L_meta_926.h49, PEqualNP.Outside.L_meta_926.h50, PEqualNP.Outside.L_meta_926.h51, PEqualNP.Outside.L_meta_926.h52, PEqualNP.Outside.L_meta_926.h53, PEqualNP.Outside.L_meta_926.h54, PEqualNP.Outside.L_meta_926.h55, PEqualNP.Outside.L_meta_926.h56, PEqualNP.Outside.L_meta_926.h57, PEqualNP.Outside.L_meta_926.h58, PEqualNP.Outside.L_meta_926.h59, PEqualNP.Outside.L_meta_926.h60, PEqualNP.Outside.L_meta_926.h61, PEqualNP.Outside.L_meta_926.h62, PEqualNP.Outside.L_meta_926.h63, PEqualNP.Outside.L_meta_926.h64, PEqualNP.Outside.L_meta_926.h65, PEqualNP.Outside.L_meta_926.h66, PEqualNP.Outside.L_meta_926.h67, PEqualNP.Outside.L_meta_926.h68, PEqualNP.Outside.L_meta_926.h69, PEqualNP.Outside.L_meta_926.h70, PEqualNP.Outside.L_meta_926.h71, PEqualNP.Outside.L_meta_926.h72, PEqualNP.Outside.L_meta_926.h73, PEqualNP.Outside.L_meta_926.h74, PEqualNP.Outside.L_meta_926.h75, PEqualNP.Outside.L_meta_926.h76, PEqualNP.Outside.L_meta_926.h77, PEqualNP.Outside.L_meta_926.h78, PEqualNP.Outside.L_meta_926.h79, PEqualNP.Outside.L_meta_926.h80, PEqualNP.Outside.L_meta_926.h81, PEqualNP.Outside.L_meta_926.h82, PEqualNP.Outside.L_meta_926.h83, PEqualNP.Outside.L_meta_926.h84⟩
