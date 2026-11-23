import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_452

open Classical in
lemma main : ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
    (∀ i, r i ≠ 0) →
    (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  intro k m r hne hred
  obtain ⟨j0, hj0⟩ := hred
  let E : Finset (Fin k) :=
    Finset.univ.filter (fun i => r i ∉ Submodule.span ℚ (r '' {j | j ≠ i}))
  have hj0E : j0 ∉ E := by
    intro h
    exact (Finset.mem_filter.mp h).2 hj0
  let s : Finset (Fin k) := insert j0 E
  have hcard : s.card = E.card + 1 := Finset.card_insert_of_notMem hj0E
  have hNat : Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} = E.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have key : ∀ (g : s → ℚ), (∑ i : s, g i • r i.1) = 0 → ∀ i : s, g i ≠ 0 →
      r i.1 ∈ Submodule.span ℚ (r '' {j | j ≠ i.1}) := by
    intro g hg i hgi
    have hsplit : g i • r i.1 = - ∑ l ∈ Finset.univ.erase i, g l • r l.1 := by
      have h1 := Finset.add_sum_erase Finset.univ (fun l : s => g l • r l.1) (Finset.mem_univ i)
      rw [hg] at h1
      exact eq_neg_of_add_eq_zero_left h1
    have hri : r i.1 = (g i)⁻¹ • (- ∑ l ∈ Finset.univ.erase i, g l • r l.1) := by
      rw [← hsplit, smul_smul, inv_mul_cancel₀ hgi, one_smul]
    rw [hri]
    apply Submodule.smul_mem
    apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro l hl
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨l.1, ?_, rfl⟩
    have hli : l ≠ i := Finset.ne_of_mem_erase hl
    intro heq
    exact hli (Subtype.ext heq)
  have hli : LinearIndependent ℚ (fun i : s => r i.1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hE : ∀ i : s, i.1 ∈ E → g i = 0 := by
      intro i hiE
      by_contra hgi
      exact (Finset.mem_filter.mp hiE).2 (key g hg i hgi)
    intro i
    by_cases hiE : i.1 ∈ E
    · exact hE i hiE
    · have hij : i.1 = j0 := by
        have := i.2
        rcases Finset.mem_insert.mp this with h | h
        · exact h
        · exact absurd h hiE
      by_contra hgi
      have hsum : (∑ l : s, g l • r l.1) = g i • r i.1 := by
        apply Finset.sum_eq_single i
        · intro l _ hl
          have hlE : l.1 ∈ E := by
            rcases Finset.mem_insert.mp l.2 with h | h
            · exact absurd (Subtype.ext (h.trans hij.symm)) hl
            · exact h
          rw [hE l hlE, zero_smul]
        · intro h
          exact absurd (Finset.mem_univ i) h
      rw [hsum] at hg
      rcases smul_eq_zero.mp hg with h | h
      · exact hgi h
      · exact hne i.1 h
  have hfin : Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i : s => r i.1))) = s.card := by
    rw [finrank_span_eq_card hli, Fintype.card_coe]
  have hmono : Submodule.span ℚ (Set.range (fun i : s => r i.1)) ≤
      Submodule.span ℚ (Set.range r) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.1, rfl⟩
  have hle := Submodule.finrank_mono hmono
  rw [hNat]
  omega

end PEqualNP.Outside.L_meta_452

theorem PEqualNP.Outside.L_meta_452 : ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
    (∀ i, r i ≠ 0) →
    (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) :=
  PEqualNP.Outside.L_meta_452.main
