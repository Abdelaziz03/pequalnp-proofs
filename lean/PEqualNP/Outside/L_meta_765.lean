import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_765

open PEqualNP.MetaComplexity

def g : (Fin 4 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)

def f : (Fin 6 → Bool) → Bool := fun x => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)

lemma size_mono (n : ℕ) (h : (Fin n → Bool) → Bool) (s s' : ℕ) (hs : s ≤ s')
    (hc : HasCircuitSize n h s) : HasCircuitSize n h s' := by
  obtain ⟨C, h1, h2, h3⟩ := hc
  exact ⟨C, h1, le_trans h2 hs, h3⟩

lemma g_nonconst : ∃ y y' : Fin 4 → Bool, g y ≠ g y' :=
  ⟨fun _ => true, fun _ => false, by simp [g]⟩

lemma f_eq : f = (fun x : Fin (2 + 4) → Bool =>
    (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) || g (fun j : Fin 4 => x (Fin.natAdd 2 j))) := by
  funext x
  have e0 : Fin.castAdd 4 (0 : Fin 2) = (0 : Fin 6) := rfl
  have e1 : Fin.castAdd 4 (1 : Fin 2) = (1 : Fin 6) := rfl
  have e2 : Fin.natAdd 2 (0 : Fin 4) = (2 : Fin 6) := rfl
  have e3 : Fin.natAdd 2 (1 : Fin 4) = (3 : Fin 6) := rfl
  have e4 : Fin.natAdd 2 (2 : Fin 4) = (4 : Fin 6) := rfl
  have e5 : Fin.natAdd 2 (3 : Fin 4) = (5 : Fin 6) := rfl
  simp only [f, g, e0, e1, e2, e3, e4, e5, Bool.or_assoc]

lemma link (s : ℕ) : HasCircuitSize 6 f (s + 2) ↔ HasCircuitSize 4 g s := by
  rw [f_eq]
  exact L153 4 s g g_nonconst

lemma main : ∀ s : ℕ, HasCircuitSize 6 f s ↔ 5 ≤ s := by
  intro s
  constructor
  · intro h
    by_contra hlt
    have h5 : HasCircuitSize 6 f (2 + 2) := size_mono 6 f s _ (by omega) h
    have h3 : HasCircuitSize 4 g 2 := (link 2).mp h5
    have h4 := (L112 2).mp h3
    omega
  · intro h
    have h3 : HasCircuitSize 4 g 3 := (L112 3).mpr (le_refl _)
    have h6 : HasCircuitSize 6 f (3 + 2) := (link 3).mpr h3
    exact size_mono 6 f _ s (by omega) h6

end PEqualNP.Outside.L_meta_765

theorem PEqualNP.Outside.L_meta_765 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s :=
  PEqualNP.Outside.L_meta_765.main
