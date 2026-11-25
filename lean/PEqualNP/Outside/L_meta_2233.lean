import Mathlib
import PEqualNP.Defs
-- The description of the OR closure (the lemmas on orSets and OrReaches) is copied from the
-- checked proof of L-meta-4183. The counting argument follows the sketch on the desk: every
-- gate of the OR closure of the output other than the output gate is read by an OR gate of
-- that closure, and an OR gate reads two wires.

namespace PEqualNP.Outside.L_meta_2233

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

-- a gate of the OR closure of a wire is the gate of that wire, or is read by an OR gate of it
lemma parent {n : ℕ} {C : Circuit} (x : ℕ) :
    ∀ w, OrReaches n C w x → w = n + x ∨
      ∃ h, OrReaches n C w h ∧ h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧
        n + x ∈ (gateAt C h).inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k x).mp hr
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hri⟩
    · exact Or.inl rfl
    · right
      rcases ih i hlt hri with rfl | ⟨h, hrh, hh, hoph, hin⟩
      · exact ⟨k, (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hk, hop, hi⟩
      · exact ⟨h, (orReaches_iff n C k h).mpr ⟨hk, Or.inr ⟨hop, i, hi, hlt, hrh⟩⟩, hh, hoph, hin⟩

theorem main (n : ℕ) (C : Circuit) (F : Finset ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j) :
    F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} + 1 := by
  classical
  let D : Finset ℕ := (Finset.range C.gates.length).filter
    (fun i => (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i)
  have hD : ∀ i, i ∈ D ↔ i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i := by
    intro i
    simp [D]
  have hset : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} = (D : Set ℕ) := by
    ext i
    simp [D]
  rw [hset, Set.ncard_coe_finset]
  have hdisj : Disjoint F D := by
    rw [Finset.disjoint_left]
    intro x hxF hxD
    have h1 := (hF x hxF).2.1
    have h2 := ((hD x).1 hxD).2.1
    rw [h1] at h2
    cases h2
  have hcardX : (F ∪ D).card = F.card + D.card := Finset.card_union_of_disjoint hdisj
  -- the gates read by a gate
  let kids : ℕ → Finset ℕ := fun h => ((gateAt C h).inputs.map (fun w => w - n)).toFinset
  have hkids : ∀ h ∈ D, (kids h).card ≤ 2 := by
    intro h hh
    have hlen := hAO.2.2 (gateAt C h) (gateAt_mem ((hD h).1 hh).1)
    calc (kids h).card ≤ ((gateAt C h).inputs.map (fun w => w - n)).length := List.toFinset_card_le _
      _ = 2 := by rw [List.length_map, hlen]
  let Y : Finset ℕ := (F ∪ D).filter (fun x => n + x ≠ C.output)
  have hYsub : Y ⊆ D.biUnion kids := by
    intro x hx
    have hxX : x ∈ F ∪ D := (Finset.mem_filter.1 hx).1
    have hne : n + x ≠ C.output := (Finset.mem_filter.1 hx).2
    have hreach : OrReaches n C C.output x := by
      rcases Finset.mem_union.1 hxX with h | h
      · exact (hF x h).2.2
      · exact ((hD x).1 h).2.2
    rcases parent x C.output hreach with h | ⟨h, hrh, hh, hoph, hin⟩
    · exact absurd h.symm hne
    · refine Finset.mem_biUnion.2 ⟨h, (hD h).2 ⟨hh, hoph, hrh⟩, ?_⟩
      exact List.mem_toFinset.2 (List.mem_map.2 ⟨n + x, hin, by omega⟩)
  have hYcard : Y.card ≤ 2 * D.card := by
    calc Y.card ≤ (D.biUnion kids).card := Finset.card_le_card hYsub
      _ ≤ ∑ h ∈ D, (kids h).card := Finset.card_biUnion_le
      _ ≤ ∑ _h ∈ D, 2 := Finset.sum_le_sum hkids
      _ = 2 * D.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hXsub : F ∪ D ⊆ Y ∪ {C.output - n} := by
    intro x hx
    by_cases h : n + x = C.output
    · exact Finset.mem_union_right _ (Finset.mem_singleton.2 (by omega))
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hx, h⟩)
  have hXcard : (F ∪ D).card ≤ Y.card + 1 := by
    calc (F ∪ D).card ≤ (Y ∪ {C.output - n}).card := Finset.card_le_card hXsub
      _ ≤ Y.card + ({C.output - n} : Finset ℕ).card := Finset.card_union_le _ _
      _ = Y.card + 1 := by rw [Finset.card_singleton]
  omega

end PEqualNP.Outside.L_meta_2233

theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 :=
  PEqualNP.Outside.L_meta_2233.main
