import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_461

lemma pickR (t x y : Fin 6) (I : Finset (Fin 6)) (h : (t = x ∨ t = y) ∧ t ∉ I)
    (hx : x ∈ I) : t = y := by
  rcases h.1 with h1 | h1
  · exact absurd (h1 ▸ hx) h.2
  · exact h1

lemma pickL (t x y : Fin 6) (I : Finset (Fin 6)) (h : (t = x ∨ t = y) ∧ t ∉ I)
    (hy : y ∈ I) : t = x := by
  rcases h.1 with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hy) h.2

lemma indP0 : ∀ f ∈ [((0 : Fin 6), (1 : Fin 6)), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)],
    ¬ (f.1 ∈ ({0, 4, 5} : Finset (Fin 6)) ∧ f.2 ∈ ({0, 4, 5} : Finset (Fin 6))) := by
  decide

lemma indP1 : ∀ f ∈ [((0 : Fin 6), (1 : Fin 6)), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)],
    ¬ (f.1 ∈ ({1, 3, 5} : Finset (Fin 6)) ∧ f.2 ∈ ({1, 3, 5} : Finset (Fin 6))) := by
  decide

lemma indP2 : ∀ f ∈ [((0 : Fin 6), (1 : Fin 6)), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)],
    ¬ (f.1 ∈ ({2, 3, 4} : Finset (Fin 6)) ∧ f.2 ∈ ({2, 3, 4} : Finset (Fin 6))) := by
  decide

lemma main : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] → ∀ τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6, (∀ e ∈ E, ∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 6 × Fin 6 → ℚ, (∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 6, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 := by
  intro E hE τ hτ c hc e he
  subst hE
  have m01 : ((0 : Fin 6), (1 : Fin 6)) ∈ [((0 : Fin 6), (1 : Fin 6)), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] := by simp
  have m02 : ((0 : Fin 6), (2 : Fin 6)) ∈ [((0 : Fin 6), (1 : Fin 6)), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] := by simp
  have m12 : ((1 : Fin 6), (2 : Fin 6)) ∈ [((0 : Fin 6), (1 : Fin 6)), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] := by simp
  have m03 : ((0 : Fin 6), (3 : Fin 6)) ∈ [((0 : Fin 6), (1 : Fin 6)), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] := by simp
  have m14 : ((1 : Fin 6), (4 : Fin 6)) ∈ [((0 : Fin 6), (1 : Fin 6)), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] := by simp
  have m25 : ((2 : Fin 6), (5 : Fin 6)) ∈ [((0 : Fin 6), (1 : Fin 6)), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] := by simp
  have P0o01 : τ (0, 1) {0, 4, 5} = 1 := pickR _ _ _ _ (hτ (0, 1) m01 {0, 4, 5} indP0) (by decide)
  have P0o02 : τ (0, 2) {0, 4, 5} = 2 := pickR _ _ _ _ (hτ (0, 2) m02 {0, 4, 5} indP0) (by decide)
  have P0f : τ (1, 2) {0, 4, 5} = 1 ∨ τ (1, 2) {0, 4, 5} = 2 := (hτ (1, 2) m12 {0, 4, 5} indP0).1
  have P0o03 : τ (0, 3) {0, 4, 5} = 3 := pickR _ _ _ _ (hτ (0, 3) m03 {0, 4, 5} indP0) (by decide)
  have P0o14 : τ (1, 4) {0, 4, 5} = 1 := pickL _ _ _ _ (hτ (1, 4) m14 {0, 4, 5} indP0) (by decide)
  have P0o25 : τ (2, 5) {0, 4, 5} = 2 := pickL _ _ _ _ (hτ (2, 5) m25 {0, 4, 5} indP0) (by decide)
  have P0s1 := hc {0, 4, 5} indP0 1
  have P0s2 := hc {0, 4, 5} indP0 2
  have P0s3 := hc {0, 4, 5} indP0 3
  have P1o01 : τ (0, 1) {1, 3, 5} = 0 := pickL _ _ _ _ (hτ (0, 1) m01 {1, 3, 5} indP1) (by decide)
  have P1f : τ (0, 2) {1, 3, 5} = 0 ∨ τ (0, 2) {1, 3, 5} = 2 := (hτ (0, 2) m02 {1, 3, 5} indP1).1
  have P1o12 : τ (1, 2) {1, 3, 5} = 2 := pickR _ _ _ _ (hτ (1, 2) m12 {1, 3, 5} indP1) (by decide)
  have P1o03 : τ (0, 3) {1, 3, 5} = 0 := pickL _ _ _ _ (hτ (0, 3) m03 {1, 3, 5} indP1) (by decide)
  have P1o14 : τ (1, 4) {1, 3, 5} = 4 := pickR _ _ _ _ (hτ (1, 4) m14 {1, 3, 5} indP1) (by decide)
  have P1o25 : τ (2, 5) {1, 3, 5} = 2 := pickL _ _ _ _ (hτ (2, 5) m25 {1, 3, 5} indP1) (by decide)
  have P1s0 := hc {1, 3, 5} indP1 0
  have P1s2 := hc {1, 3, 5} indP1 2
  have P1s4 := hc {1, 3, 5} indP1 4
  have P2f : τ (0, 1) {2, 3, 4} = 0 ∨ τ (0, 1) {2, 3, 4} = 1 := (hτ (0, 1) m01 {2, 3, 4} indP2).1
  have P2o02 : τ (0, 2) {2, 3, 4} = 0 := pickL _ _ _ _ (hτ (0, 2) m02 {2, 3, 4} indP2) (by decide)
  have P2o12 : τ (1, 2) {2, 3, 4} = 1 := pickL _ _ _ _ (hτ (1, 2) m12 {2, 3, 4} indP2) (by decide)
  have P2o03 : τ (0, 3) {2, 3, 4} = 0 := pickL _ _ _ _ (hτ (0, 3) m03 {2, 3, 4} indP2) (by decide)
  have P2o14 : τ (1, 4) {2, 3, 4} = 1 := pickL _ _ _ _ (hτ (1, 4) m14 {2, 3, 4} indP2) (by decide)
  have P2o25 : τ (2, 5) {2, 3, 4} = 5 := pickR _ _ _ _ (hτ (2, 5) m25 {2, 3, 4} indP2) (by decide)
  have P2s0 := hc {2, 3, 4} indP2 0
  have P2s1 := hc {2, 3, 4} indP2 1
  have P2s5 := hc {2, 3, 4} indP2 5
  have hall : c (0, 1) = 0 ∧ c (0, 2) = 0 ∧ c (1, 2) = 0 ∧ c (0, 3) = 0 ∧ c (1, 4) = 0 ∧
      c (2, 5) = 0 := by
    rcases P0f with h | h <;> rcases P1f with h' | h' <;> rcases P2f with h'' | h'' <;>
      simp [P0o01, P0o02, P0o03, P0o14, P0o25, h] at P0s1 P0s2 P0s3 <;>
      simp [P1o01, P1o12, P1o03, P1o14, P1o25, h'] at P1s0 P1s2 P1s4 <;>
      simp [P2o02, P2o12, P2o03, P2o14, P2o25, h''] at P2s0 P2s1 P2s5 <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2.1
  · exact hall.2.2.2.1
  · exact hall.2.2.2.2.1
  · exact hall.2.2.2.2.2

end PEqualNP.Outside.L_meta_461

theorem PEqualNP.Outside.L_meta_461 : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] → ∀ τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6, (∀ e ∈ E, ∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 6 × Fin 6 → ℚ, (∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 6, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 :=
  PEqualNP.Outside.L_meta_461.main
