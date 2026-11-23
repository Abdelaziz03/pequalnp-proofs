import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_229

open PEqualNP.MetaComplexity

def orF (n : ℕ) : (Fin n → Bool) → Bool := fun x => decide (∃ i : Fin n, x i = true)

def zeros (n : ℕ) : Fin n → Bool := fun _ => false

def pt {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

lemma orF_true (n : ℕ) (x : Fin n → Bool) : orF n x = true ↔ ∃ i : Fin n, x i = true := by
  unfold orF
  exact decide_eq_true_iff

lemma orF_false (n : ℕ) (y : Fin n → Bool) : orF n y = false ↔ y = zeros n := by
  unfold orF zeros
  rw [decide_eq_false_iff_not]
  constructor
  · intro h
    funext i
    cases hi : y i with
    | false => rfl
    | true => exact absurd ⟨i, hi⟩ h
  · intro h hex
    obtain ⟨i, hi⟩ := hex
    rw [h] at hi
    exact absurd hi (by simp)

noncomputable def tau (n : ℕ) (x _y : Fin n → Bool) : ℕ :=
  if h : ∃ i : Fin n, x i = true then ((Classical.choose h : Fin n) : ℕ) else 0

lemma tau_spec (n : ℕ) (x y : Fin n → Bool) (hex : ∃ i : Fin n, x i = true) :
    ∃ i : Fin n, tau n x y = (i : ℕ) ∧ x i = true := by
  refine ⟨Classical.choose hex, ?_, Classical.choose_spec hex⟩
  unfold tau
  rw [dif_pos hex]

lemma upper (n : ℕ) : HasTypedRank n (orF n) n := by
  classical
  refine ⟨tau n, ?_, ?_⟩
  · intro x y hx hy
    obtain ⟨i, hti, hxi⟩ := tau_spec n x y ((orF_true n x).mp hx)
    refine ⟨i, hti, ?_⟩
    have h2 : y = zeros n := (orF_false n y).mp hy
    rw [hxi, h2]
    simp [zeros]
  · have hneg : ∀ i : Fin n, typedMatrix n (orF n) (tau n) i false = 0 := by
      intro i
      ext x y
      simp only [typedMatrix, Matrix.zero_apply]
      apply if_neg
      intro hcon
      obtain ⟨hx, _, ht, hxi⟩ := hcon
      obtain ⟨j, htj, hxj⟩ := tau_spec n x y ((orF_true n x).mp hx)
      have hji : j = i := by
        apply Fin.ext
        rw [← htj, ht]
      rw [hji, hxi] at hxj
      exact absurd hxj (by simp)
    have hpos : ∀ i : Fin n, (typedMatrix n (orF n) (tau n) i true).rank ≤ 1 := by
      intro i
      rw [← Matrix.rank_transpose]
      apply le_trans (Matrix.rank_le_card_of_support_subset _ {zeros n} ?_) (by simp)
      apply Function.support_subset_iff'.mpr
      intro y hy
      have hy' : orF n y ≠ false := by
        intro h
        apply hy
        rw [(orF_false n y).mp h]
        simp
      funext x
      simp [Matrix.row, Matrix.transpose_apply, typedMatrix, hy']
    calc ∑ i : Fin n, ∑ b : Bool, (typedMatrix n (orF n) (tau n) i b).rank
        ≤ ∑ _i : Fin n, 1 := by
          apply Finset.sum_le_sum
          intro i _
          rw [Fintype.sum_bool, hneg i, Matrix.rank_zero, Nat.add_zero]
          exact hpos i
      _ = n := by simp

lemma lower (n : ℕ) (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) (hτ : IsTyping n (orF n) τ) :
    n ≤ ∑ i : Fin n, ∑ b : Bool, (typedMatrix n (orF n) τ i b).rank := by
  classical
  have hone : ∀ i : Fin n, 1 ≤ (typedMatrix n (orF n) τ i true).rank := by
    intro i
    have hx : orF n (pt i) = true := (orF_true n (pt i)).mpr ⟨i, by simp [pt]⟩
    have hy : orF n (zeros n) = false := (orF_false n (zeros n)).mpr rfl
    obtain ⟨j, hj, hd⟩ := hτ (pt i) (zeros n) hx hy
    have hji : j = i := by
      by_contra hne
      apply hd
      simp [pt, zeros, hne]
    rw [hji] at hj
    have hentry : typedMatrix n (orF n) τ i true (pt i) (zeros n) = 1 := by
      unfold typedMatrix
      apply if_pos
      exact ⟨hx, hy, hj, by simp [pt]⟩
    have hsub : (typedMatrix n (orF n) τ i true).submatrix (fun _ : Unit => pt i)
        (fun _ : Unit => zeros n) = 1 := by
      ext a b
      simp [Matrix.submatrix_apply, Matrix.one_apply, hentry]
    have hle := Matrix.rank_submatrix_le (typedMatrix n (orF n) τ i true)
      (fun _ : Unit => pt i) (fun _ : Unit => zeros n)
    rw [hsub] at hle
    simpa using hle
  calc n = ∑ _i : Fin n, 1 := by simp
    _ ≤ ∑ i : Fin n, ∑ b : Bool, (typedMatrix n (orF n) τ i b).rank := by
        apply Finset.sum_le_sum
        intro i _
        rw [Fintype.sum_bool]
        have := hone i
        omega

lemma main (n : ℕ) (hn : 1 ≤ n) :
    HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) n ∧
    ¬ HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) (n - 1) := by
  refine ⟨upper n, ?_⟩
  intro hcon
  obtain ⟨τ, hτ, hsum⟩ := hcon
  have h := lower n τ hτ
  have h2 : n ≤ n - 1 := le_trans h hsum
  omega

end PEqualNP.Outside.L_meta_229

theorem PEqualNP.Outside.L_meta_229 : ∀ n : ℕ, 1 ≤ n → PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) n ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) (n - 1) :=
  PEqualNP.Outside.L_meta_229.main
