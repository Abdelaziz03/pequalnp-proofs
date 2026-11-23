import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_455

lemma main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) →
    (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
    ∀ u v : Fin n, G.Adj u v →
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj u w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj u w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v), ¬ G.Adj a b) := by
  intro n G _ htri hc4 u v huv
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    exact htri v a b ⟨ha.2, hab, hb.2.symm⟩
  · intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    exact htri u a b ⟨ha.2, hab, hb.2.symm⟩
  · intro a ha b hb hab
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at ha hb
    rcases ha with ⟨_, hva, hau⟩ | ⟨_, hua, hav⟩ <;> rcases hb with ⟨_, hvb, hbu⟩ | ⟨_, hub, hbv⟩
    · exact htri v a b ⟨hva, hab, hvb.symm⟩
    · exact hc4 v a b u (Ne.symm hbv) hau ⟨hva, hab, hub.symm, huv⟩
    · exact hc4 u a b v (Ne.symm hbu) hav ⟨hua, hab, hvb.symm, huv.symm⟩
    · exact htri u a b ⟨hua, hab, hub.symm⟩

end PEqualNP.Outside.L_meta_455

theorem PEqualNP.Outside.L_meta_455 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) →
    (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
    ∀ u v : Fin n, G.Adj u v →
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj u w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj u w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v), ¬ G.Adj a b) :=
  PEqualNP.Outside.L_meta_455.main
