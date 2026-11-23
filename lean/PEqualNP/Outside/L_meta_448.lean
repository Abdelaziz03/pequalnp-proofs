import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_448

lemma no_loop (m k : ℕ) (hk : 1 ≤ k) (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k)
    (x : Fin (m + 2 * k * (m * m)))
    (h1 : (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
      (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (h2 : (p + 1 = 0 ∧ x.val = u.val) ∨ (p + 1 = 2 * k + 1 ∧ x.val = v.val) ∨
      (1 ≤ p + 1 ∧ p + 1 ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + (p + 1))) :
    False := by
  have hu := u.isLt
  have hv := v.isLt
  generalize 2 * k * (u.val * m + v.val) = B at h1 h2
  rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ <;>
    rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2, b3⟩ <;> omega

lemma main : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → ∃ S : SimpleGraph (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) := by
  intro m k H Q hk hQ
  have hsymm : Std.Symm (fun x y : Fin (m + 2 * k * (m * m)) =>
      ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
        ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) := by
    refine ⟨?_⟩
    intro x y h
    obtain ⟨u, v, huv, hadj, p, hp, h⟩ := h
    exact ⟨u, v, huv, hadj, p, hp, h.symm⟩
  have hloop : Std.Irrefl (fun x y : Fin (m + 2 * k * (m * m)) =>
      ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
        ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) := by
    refine ⟨?_⟩
    intro x h
    obtain ⟨u, v, huv, hadj, p, hp, h⟩ := h
    have h12 : Q u v p x ∧ Q u v (p + 1) x := by
      rcases h with h | h <;> exact h
    obtain ⟨h1, h2⟩ := h12
    rw [hQ] at h1 h2
    exact no_loop m k hk u v p hp x h1 h2
  exact ⟨SimpleGraph.mk _ hsymm hloop, fun x y => Iff.rfl⟩

end PEqualNP.Outside.L_meta_448

theorem PEqualNP.Outside.L_meta_448 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → ∃ S : SimpleGraph (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) :=
  PEqualNP.Outside.L_meta_448.main
