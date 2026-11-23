import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_457

lemma pickR (t x y i : Fin 3) (h : (t = x ∨ t = y) ∧ t ∉ ({i} : Finset (Fin 3)))
    (hx : x = i) : t = y := by
  rcases h.1 with h1 | h1
  · exact absurd (by rw [h1, hx]; exact Finset.mem_singleton_self i) h.2
  · exact h1

lemma pickL (t x y i : Fin 3) (h : (t = x ∨ t = y) ∧ t ∉ ({i} : Finset (Fin 3)))
    (hy : y = i) : t = x := by
  rcases h.1 with h1 | h1
  · exact h1
  · exact absurd (by rw [h1, hy]; exact Finset.mem_singleton_self i) h.2

lemma ind : ∀ i : Fin 3, ∀ f ∈ [((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)],
    ¬ (f.1 ∈ ({i} : Finset (Fin 3)) ∧ f.2 ∈ ({i} : Finset (Fin 3))) := by
  decide

lemma main : ∀ E : List (Fin 3 × Fin 3), E = [(0, 1), (0, 2), (1, 2)] → ∀ τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3, (∀ e ∈ E, ∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 3 × Fin 3 → ℚ, (∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 3, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 := by
  intro E hE τ hτ c hc e he
  subst hE
  have m01 : ((0 : Fin 3), (1 : Fin 3)) ∈ [((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)] := by simp
  have m02 : ((0 : Fin 3), (2 : Fin 3)) ∈ [((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)] := by simp
  have m12 : ((1 : Fin 3), (2 : Fin 3)) ∈ [((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)] := by simp
  have A1 : τ (0, 1) {0} = 1 := pickR _ _ _ _ (hτ (0, 1) m01 {0} (ind 0)) rfl
  have A2 : τ (0, 2) {0} = 2 := pickR _ _ _ _ (hτ (0, 2) m02 {0} (ind 0)) rfl
  have A3 : τ (1, 2) {0} = 1 ∨ τ (1, 2) {0} = 2 := (hτ (1, 2) m12 {0} (ind 0)).1
  have B1 : τ (0, 1) {1} = 0 := pickL _ _ _ _ (hτ (0, 1) m01 {1} (ind 1)) rfl
  have B2 : τ (1, 2) {1} = 2 := pickR _ _ _ _ (hτ (1, 2) m12 {1} (ind 1)) rfl
  have B3 : τ (0, 2) {1} = 0 ∨ τ (0, 2) {1} = 2 := (hτ (0, 2) m02 {1} (ind 1)).1
  have C1 : τ (0, 2) {2} = 0 := pickL _ _ _ _ (hτ (0, 2) m02 {2} (ind 2)) rfl
  have C2 : τ (1, 2) {2} = 1 := pickL _ _ _ _ (hτ (1, 2) m12 {2} (ind 2)) rfl
  have C3 : τ (0, 1) {2} = 0 ∨ τ (0, 1) {2} = 1 := (hτ (0, 1) m01 {2} (ind 2)).1
  have s1 := hc {0} (ind 0) 1
  have s2 := hc {0} (ind 0) 2
  have s3 := hc {1} (ind 1) 0
  have s4 := hc {1} (ind 1) 2
  have s5 := hc {2} (ind 2) 0
  have s6 := hc {2} (ind 2) 1
  have hall : c (0, 1) = 0 ∧ c (0, 2) = 0 ∧ c (1, 2) = 0 := by
    rcases A3 with h | h <;> rcases B3 with h' | h' <;> rcases C3 with h'' | h'' <;>
      simp [A1, A2, h, B1, B2, h', C1, C2, h''] at s1 s2 s3 s4 s5 s6 <;>
      refine ⟨?_, ?_, ?_⟩ <;> linarith
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2

end PEqualNP.Outside.L_meta_457

theorem PEqualNP.Outside.L_meta_457 : ∀ E : List (Fin 3 × Fin 3), E = [(0, 1), (0, 2), (1, 2)] → ∀ τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3, (∀ e ∈ E, ∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 3 × Fin 3 → ℚ, (∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 3, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 :=
  PEqualNP.Outside.L_meta_457.main
