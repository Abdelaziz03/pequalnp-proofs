import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764

open PEqualNP.MetaComplexity

def g : (Fin 3 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

def f : (Fin 5 → Bool) → Bool := fun x => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)

lemma size_mono (n : ℕ) (h : (Fin n → Bool) → Bool) (s s' : ℕ) (hs : s ≤ s')
    (hc : HasCircuitSize n h s) : HasCircuitSize n h s' := by
  obtain ⟨C, h1, h2, h3⟩ := hc
  exact ⟨C, h1, le_trans h2 hs, h3⟩

lemma g_nonconst : ∃ y y' : Fin 3 → Bool, g y ≠ g y' :=
  ⟨fun _ => true, fun _ => false, by simp [g]⟩

lemma f_eq : f = (fun x : Fin (2 + 3) → Bool =>
    (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || g (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
  funext x
  have e0 : Fin.castAdd 3 (0 : Fin 2) = (0 : Fin 5) := rfl
  have e1 : Fin.castAdd 3 (1 : Fin 2) = (1 : Fin 5) := rfl
  have e2 : Fin.natAdd 2 (0 : Fin 3) = (2 : Fin 5) := rfl
  have e3 : Fin.natAdd 2 (1 : Fin 3) = (3 : Fin 5) := rfl
  have e4 : Fin.natAdd 2 (2 : Fin 3) = (4 : Fin 5) := rfl
  simp only [f, g, e0, e1, e2, e3, e4, Bool.or_assoc]

lemma link (s : ℕ) : HasCircuitSize 5 f (s + 2) ↔ HasCircuitSize 3 g s := by
  rw [f_eq]
  exact L153 3 s g g_nonconst

lemma main : ∀ s : ℕ, HasCircuitSize 5 f s ↔ 6 ≤ s := by
  intro s
  constructor
  · intro h
    by_contra hlt
    have h5 : HasCircuitSize 5 f (3 + 2) := size_mono 5 f s _ (by omega) h
    have h3 : HasCircuitSize 3 g 3 := (link 3).mp h5
    have h4 := (L100 3).mp h3
    omega
  · intro h
    have h3 : HasCircuitSize 3 g 4 := (L100 4).mpr (le_refl _)
    have h6 : HasCircuitSize 5 f (4 + 2) := (link 4).mpr h3
    exact size_mono 5 f _ s (by omega) h6

end PEqualNP.Outside.L_meta_764

theorem PEqualNP.Outside.L_meta_764 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s :=
  PEqualNP.Outside.L_meta_764.main
