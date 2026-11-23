import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_278

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_app_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_app_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_big (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_app_lt w _ i hi

lemma fold_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i =>
        if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [fold_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false =
          g0.op.eval (g0.inputs.map fun i => w.getD i false) := getD_app_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ite_true, fold_getD_lt gs (step w g0) i hilt]
        exact (getD_app_lt w _ i hi).symm
      · simp only [hi, ite_false]
        exact getD_big w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

def W {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

lemma W_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    W C x i = x ⟨i, hi⟩ := by
  unfold W
  change (C.gates.foldl step (List.ofFn x)).getD i false = _
  rw [fold_getD_lt C.gates (List.ofFn x) i (by simp [hi])]
  simp [List.getD_eq_getElem?_getD, hi]

lemma W_big {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : n + C.gates.length ≤ i) :
    W C x i = false := by
  unfold W
  change (C.gates.foldl step (List.ofFn x)).getD i false = _
  apply getD_big
  rw [fold_len]
  simpa using hi

lemma W_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    W C x (n + j) = g.op.eval (g.inputs.map fun i => if i < n + j then W C x i else false) := by
  have h := fold_gate C.gates (List.ofFn x) j g hj
  simp only [List.length_ofFn] at h
  exact h

def ch {n : ℕ} (C : Circuit) (m : ℕ) (x : Fin n → Bool) (i : ℕ) : Bool :=
  if i < m then W C x i else false

lemma W_and {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) (hop : g.op = GateOp.and) (hin : g.inputs = [a, b]) :
    W C x (n + j) = (ch C (n + j) x a && ch C (n + j) x b) := by
  rw [W_gate C x j g hj, hop, hin]
  simp [GateOp.eval, ch]

lemma W_or {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) (hop : g.op = GateOp.or) (hin : g.inputs = [a, b]) :
    W C x (n + j) = (ch C (n + j) x a || ch C (n + j) x b) := by
  rw [W_gate C x j g hj, hop, hin]
  simp [GateOp.eval, ch]

def Good (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

lemma gate_shape (C : Circuit) (hC : Good C) (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] := by
  have hmem : g ∈ C.gates := List.mem_of_getElem? hj
  obtain ⟨hop, hlen⟩ := hC g hmem
  exact ⟨hop, List.length_eq_two.mp hlen⟩

lemma W_mono {n : ℕ} (C : Circuit) (hC : Good C) (x y : Fin n → Bool)
    (hxy : ∀ q, x q = true → y q = true) :
    ∀ i : ℕ, W C x i = true → W C y i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < n
    · rw [W_input C x i h1, W_input C y i h1]
      exact hxy ⟨i, h1⟩
    · by_cases h2 : n + C.gates.length ≤ i
      · rw [W_big C x i h2]
        intro h
        exact absurd h (by simp)
      · have hjlt : i - n < C.gates.length := by omega
        have hij : i = n + (i - n) := by omega
        have hg : C.gates[i - n]? = some (C.gates[i - n]'hjlt) := List.getElem?_eq_getElem hjlt
        obtain ⟨hop, a, b, hin⟩ := gate_shape C hC (i - n) _ hg
        have hch : ∀ c : ℕ, ch C (n + (i - n)) x c = true → ch C (n + (i - n)) y c = true := by
          intro c hc
          unfold ch at hc ⊢
          by_cases hlt : c < n + (i - n)
          · simp only [hlt, ite_true] at hc ⊢
            exact ih c (by omega) hc
          · simp only [hlt, ite_false] at hc
            exact absurd hc (by simp)
        rw [hij]
        rcases hop with hop | hop
        · rw [W_and C x _ a b _ hg hop hin, W_and C y _ a b _ hg hop hin]
          intro h
          rw [Bool.and_eq_true] at h ⊢
          exact ⟨hch a h.1, hch b h.2⟩
        · rw [W_or C x _ a b _ hg hop hin, W_or C y _ a b _ hg hop hin]
          intro h
          rw [Bool.or_eq_true] at h ⊢
          rcases h with h | h
          · exact Or.inl (hch a h)
          · exact Or.inr (hch b h)

def pt {n : ℕ} (p : Fin n) : Fin n → Bool := fun q => decide (q = p)

def ind {n : ℕ} (Y : Finset (Fin n)) : Fin n → Bool := fun q => decide (q ∈ Y)

def A {n : ℕ} (C : Circuit) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p : Fin n =>
    (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD i false = true)

lemma mem_A {n : ℕ} (C : Circuit) (i : ℕ) (p : Fin n) :
    p ∈ A C i ↔ W C (pt p) i = true := by
  unfold A
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ p, h⟩⟩

lemma A_input {n : ℕ} (C : Circuit) (i : ℕ) (hi : i < n) :
    (A C i : Finset (Fin n)) = {⟨i, hi⟩} := by
  ext p
  rw [mem_A, W_input C (pt p) i hi]
  simp only [pt, decide_eq_true_eq, Finset.mem_singleton]
  exact eq_comm

lemma A_big {n : ℕ} (C : Circuit) (i : ℕ) (hi : n + C.gates.length ≤ i) :
    (A C i : Finset (Fin n)) = ∅ := by
  ext p
  rw [mem_A, W_big C (pt p) i hi]
  simp

def chA {n : ℕ} (C : Circuit) (m i : ℕ) : Finset (Fin n) :=
  if i < m then A C i else ∅

lemma mem_chA {n : ℕ} (C : Circuit) (m i : ℕ) (p : Fin n) :
    p ∈ chA C m i ↔ ch C m (pt p) i = true := by
  unfold chA ch
  by_cases h : i < m
  · simp only [h, ite_true]
    exact mem_A C i p
  · simp [h]

lemma A_and {n : ℕ} (C : Circuit) (j a b : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) (hop : g.op = GateOp.and) (hin : g.inputs = [a, b]) :
    (A C (n + j) : Finset (Fin n)) = chA C (n + j) a ∩ chA C (n + j) b := by
  ext p
  rw [mem_A, W_and C (pt p) j a b g hj hop hin, Finset.mem_inter, mem_chA, mem_chA,
    Bool.and_eq_true]

lemma A_or {n : ℕ} (C : Circuit) (j a b : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) (hop : g.op = GateOp.or) (hin : g.inputs = [a, b]) :
    (A C (n + j) : Finset (Fin n)) = chA C (n + j) a ∪ chA C (n + j) b := by
  ext p
  rw [mem_A, W_or C (pt p) j a b g hj hop hin, Finset.mem_union, mem_chA, mem_chA,
    Bool.or_eq_true]

def Priv {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (i : ℕ) : Prop :=
  A C i ⊆ S ∧ 2 ≤ (A C i : Finset (Fin n)).card

open Classical in
noncomputable def node {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (m : ℕ) (prev : ℕ → Bool) :
    Bool :=
  if ¬ ((A C m : Finset (Fin n)) ⊆ S) then true
  else if (A C m : Finset (Fin n)).card ≤ 1 then false
  else match C.gates[m - n]? with
    | none => false
    | some g => g.op.eval (g.inputs.map prev)

noncomputable def vt {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : ℕ → ℕ → Bool
  | 0, _ => false
  | m + 1, i => if i = m then node C S m (vt C S m) else vt C S m i

noncomputable def v {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (i : ℕ) : Bool :=
  node C S i (vt C S i)

lemma vt_ge {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (m i : ℕ) (h : m ≤ i) :
    vt C S m i = false := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hne : i ≠ m := by omega
    simp only [vt, hne, ite_false]
    exact ih (by omega)

lemma vt_lt {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (m i : ℕ) (h : i < m) :
    vt C S m i = v C S i := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hi : i = m
    · subst hi
      simp only [vt, ite_true]
      rfl
    · simp only [vt, hi, ite_false]
      exact ih (by omega)

lemma vt_true {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (m i : ℕ) (h : vt C S m i = true) :
    i < m ∧ v C S i = true := by
  by_cases hi : i < m
  · exact ⟨hi, by rw [← vt_lt C S m i hi]; exact h⟩
  · rw [vt_ge C S m i (by omega)] at h
    exact absurd h (by simp)

open Classical in
noncomputable def pc {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun i => Priv C S i)).card

lemma pc_succ_le {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (m : ℕ) :
    pc C S m ≤ pc C S (m + 1) := by
  classical
  unfold pc
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_subset_range.mpr (Nat.le_succ m)

lemma pc_succ_priv {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (m : ℕ) (h : Priv C S m) :
    pc C S (m + 1) = pc C S m + 1 := by
  classical
  unfold pc
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem]
  simp

lemma pc_mono {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (m m' : ℕ) (h : m ≤ m') :
    pc C S m ≤ pc C S m' := by
  classical
  unfold pc
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_subset_range.mpr h

lemma priv_is_gate {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (m : ℕ) (h : Priv C S m) :
    n ≤ m ∧ m - n < C.gates.length := by
  obtain ⟨_, h2⟩ := h
  have h1 : n ≤ m := by
    by_contra hlt
    rw [A_input C m (by omega)] at h2
    simp at h2
  refine ⟨h1, ?_⟩
  by_contra hge
  rw [A_big C m (by omega)] at h2
  simp at h2

lemma pc_le_count {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (m : ℕ) :
    pc C S m ≤ ((Finset.range C.size).filter (fun j =>
      (A C (n + j) : Finset (Fin n)) ⊆ S ∧ 2 ≤ (A C (n + j) : Finset (Fin n)).card)).card := by
  classical
  unfold pc
  apply Finset.card_le_card_of_injOn (fun i => i - n)
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨_, hp⟩ := hi
    obtain ⟨h1, h2⟩ := priv_is_gate C S i hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨h2, ?_⟩
    have he : n + (i - n) = i := by omega
    rw [he]
    exact hp
  · intro i hi i' hi' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hi hi'
    obtain ⟨h1, _⟩ := priv_is_gate C S i hi.2
    obtain ⟨h1', _⟩ := priv_is_gate C S i' hi'.2
    simp only at heq
    omega

lemma node_cases {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (m : ℕ) (prev : ℕ → Bool) :
    (¬ ((A C m : Finset (Fin n)) ⊆ S) ∧ node C S m prev = true) ∨
    ((A C m : Finset (Fin n)) ⊆ S ∧ (A C m : Finset (Fin n)).card ≤ 1 ∧ node C S m prev = false) ∨
    (Priv C S m ∧ ∃ g : Gate, C.gates[m - n]? = some g ∧
      node C S m prev = g.op.eval (g.inputs.map prev)) := by
  classical
  by_cases h1 : (A C m : Finset (Fin n)) ⊆ S
  · by_cases h2 : (A C m : Finset (Fin n)).card ≤ 1
    · right; left
      refine ⟨h1, h2, ?_⟩
      unfold node
      simp [h1, h2]
    · right; right
      have hp : Priv C S m := ⟨h1, by omega⟩
      obtain ⟨_, hlt⟩ := priv_is_gate C S m hp
      refine ⟨hp, C.gates[m - n]'hlt, List.getElem?_eq_getElem hlt, ?_⟩
      unfold node
      simp [h1, h2, List.getElem?_eq_getElem hlt]
  · left
    refine ⟨h1, ?_⟩
    unfold node
    simp [h1]

lemma W_ind_of_mem {n : ℕ} (C : Circuit) (hC : Good C) (Y : Finset (Fin n)) (y : Fin n)
    (hy : y ∈ Y) (i : ℕ) (h : y ∈ (A C i : Finset (Fin n))) : W C (ind Y) i = true := by
  rw [mem_A] at h
  apply W_mono C hC (pt y) (ind Y) _ i h
  intro q hq
  simp only [pt, decide_eq_true_eq] at hq
  subst hq
  simp [ind, hy]

lemma W_ind_mono {n : ℕ} (C : Circuit) (hC : Good C) (Y Y' : Finset (Fin n)) (hYY : Y ⊆ Y')
    (i : ℕ) (h : W C (ind Y) i = true) : W C (ind Y') i = true := by
  apply W_mono C hC (ind Y) (ind Y') _ i h
  intro q hq
  simp only [ind, decide_eq_true_eq] at hq ⊢
  exact hYY hq

lemma lemA {n : ℕ} (C : Circuit) (hC : Good C) (S : Finset (Fin n)) :
    ∀ m : ℕ, ∀ R : Finset ℕ, (∀ w ∈ R, w < m ∧ v C S w = true) →
      ∃ Y : Finset (Fin n), Disjoint Y S ∧ (∀ w ∈ R, W C (ind Y) w = true) ∧
        Y.card ≤ pc C S m + R.card := by
  classical
  intro m
  induction m with
  | zero =>
    intro R hR
    have hRe : R = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro w hw
      exact absurd (hR w hw).1 (by omega)
    subst hRe
    exact ⟨∅, Finset.disjoint_empty_left S, by simp, by simp⟩
  | succ m ih =>
    intro R hR
    by_cases hm : m ∈ R
    · have hvm : v C S m = true := (hR m hm).2
      have hR0 : ∀ w ∈ R.erase m, w < m ∧ v C S w = true := by
        intro w hw
        have hne : w ≠ m := Finset.ne_of_mem_erase hw
        have hw' := hR w (Finset.mem_of_mem_erase hw)
        exact ⟨by omega, hw'.2⟩
      have hcard : (R.erase m).card + 1 = R.card := Finset.card_erase_add_one hm
      rcases node_cases C S m (vt C S m) with ⟨hleave, _⟩ | ⟨_, _, hfalse⟩ | ⟨hpriv, g, hg, hnode⟩
      · obtain ⟨y, hyA, hyS⟩ := Finset.not_subset.mp hleave
        obtain ⟨Y0, hd, hw0, hc0⟩ := ih (R.erase m) hR0
        refine ⟨insert y Y0, ?_, ?_, ?_⟩
        · rw [Finset.disjoint_insert_left]
          exact ⟨hyS, hd⟩
        · intro w hw
          by_cases hwm : w = m
          · rw [hwm]
            exact W_ind_of_mem C hC _ y (Finset.mem_insert_self y Y0) m hyA
          · exact W_ind_mono C hC Y0 _ (Finset.subset_insert y Y0) w
              (hw0 w (Finset.mem_erase.mpr ⟨hwm, hw⟩))
        · have h1 : (insert y Y0).card ≤ Y0.card + 1 := Finset.card_insert_le y Y0
          have h2 := pc_succ_le C S m
          omega
      · have : v C S m = false := hfalse
        rw [this] at hvm
        exact absurd hvm (by simp)
      · obtain ⟨hnm, hlt⟩ := priv_is_gate C S m hpriv
        have hmn : n + (m - n) = m := by omega
        obtain ⟨hop, a, b, hin⟩ := gate_shape C hC (m - n) g hg
        have hval : g.op.eval (g.inputs.map (vt C S m)) = true := by
          rw [← hnode]
          exact hvm
        have hpcs := pc_succ_priv C S m hpriv
        rcases hop with hop | hop
        · rw [hop, hin] at hval
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            Bool.and_true, id_eq, Bool.and_eq_true] at hval
          obtain ⟨ha, hb⟩ := hval
          obtain ⟨halt, hav⟩ := vt_true C S m a ha
          obtain ⟨hblt, hbv⟩ := vt_true C S m b hb
          have hR' : ∀ w ∈ insert a (insert b (R.erase m)), w < m ∧ v C S w = true := by
            intro w hw
            rw [Finset.mem_insert, Finset.mem_insert] at hw
            rcases hw with rfl | rfl | hw
            · exact ⟨halt, hav⟩
            · exact ⟨hblt, hbv⟩
            · exact hR0 w hw
          obtain ⟨Y, hd, hwY, hcY⟩ := ih _ hR'
          refine ⟨Y, hd, ?_, ?_⟩
          · intro w hw
            by_cases hwm : w = m
            · rw [hwm]
              have hWa : W C (ind Y) a = true := hwY a (Finset.mem_insert_self _ _)
              have hWb : W C (ind Y) b = true :=
                hwY b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
              have hEq := W_and C (ind Y) (m - n) a b g hg hop hin
              rw [hmn] at hEq
              rw [hEq]
              simp [ch, halt, hblt, hWa, hWb]
            · exact hwY w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_erase.mpr ⟨hwm, hw⟩)))
          · have h1 : (insert a (insert b (R.erase m))).card ≤ (R.erase m).card + 2 := by
              have h3 := Finset.card_insert_le a (insert b (R.erase m))
              have h4 := Finset.card_insert_le b (R.erase m)
              omega
            omega
        · rw [hop, hin] at hval
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            Bool.or_false, id_eq, Bool.or_eq_true] at hval
          have hone : ∃ c : ℕ, (c = a ∨ c = b) ∧ c < m ∧ v C S c = true := by
            rcases hval with ha | hb
            · obtain ⟨h1, h2⟩ := vt_true C S m a ha
              exact ⟨a, Or.inl rfl, h1, h2⟩
            · obtain ⟨h1, h2⟩ := vt_true C S m b hb
              exact ⟨b, Or.inr rfl, h1, h2⟩
          obtain ⟨c, hcab, hclt, hcv⟩ := hone
          have hR' : ∀ w ∈ insert c (R.erase m), w < m ∧ v C S w = true := by
            intro w hw
            rw [Finset.mem_insert] at hw
            rcases hw with rfl | hw
            · exact ⟨hclt, hcv⟩
            · exact hR0 w hw
          obtain ⟨Y, hd, hwY, hcY⟩ := ih _ hR'
          refine ⟨Y, hd, ?_, ?_⟩
          · intro w hw
            by_cases hwm : w = m
            · rw [hwm]
              have hWc : W C (ind Y) c = true := hwY c (Finset.mem_insert_self _ _)
              have hEq := W_or C (ind Y) (m - n) a b g hg hop hin
              rw [hmn] at hEq
              rw [hEq, Bool.or_eq_true]
              rcases hcab with rfl | rfl
              · left; simp [ch, hclt, hWc]
              · right; simp [ch, hclt, hWc]
            · exact hwY w (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwm, hw⟩))
          · have h1 : (insert c (R.erase m)).card ≤ (R.erase m).card + 1 :=
              Finset.card_insert_le c (R.erase m)
            omega
    · have hR0 : ∀ w ∈ R, w < m ∧ v C S w = true := by
        intro w hw
        have hne : w ≠ m := fun h => hm (h ▸ hw)
        have hw' := hR w hw
        exact ⟨by omega, hw'.2⟩
      obtain ⟨Y, hd, hwY, hcY⟩ := ih R hR0
      have h2 := pc_succ_le C S m
      exact ⟨Y, hd, hwY, by omega⟩

lemma lemB {n : ℕ} (C : Circuit) (hC : Good C) (S : Finset (Fin n)) :
    ∀ m : ℕ, ∀ R : Finset ℕ, (∀ w ∈ R, w < m ∧ v C S w = false) →
      (R.biUnion (fun w => (A C w : Finset (Fin n)))).card ≤ pc C S m + R.card := by
  classical
  intro m
  induction m with
  | zero =>
    intro R hR
    have hRe : R = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro w hw
      exact absurd (hR w hw).1 (by omega)
    subst hRe
    simp
  | succ m ih =>
    intro R hR
    by_cases hm : m ∈ R
    · have hvm : v C S m = false := (hR m hm).2
      have hR0 : ∀ w ∈ R.erase m, w < m ∧ v C S w = false := by
        intro w hw
        have hne : w ≠ m := Finset.ne_of_mem_erase hw
        have hw' := hR w (Finset.mem_of_mem_erase hw)
        exact ⟨by omega, hw'.2⟩
      have hcard : (R.erase m).card + 1 = R.card := Finset.card_erase_add_one hm
      have hsplit : R.biUnion (fun w => (A C w : Finset (Fin n))) =
          A C m ∪ (R.erase m).biUnion (fun w => (A C w : Finset (Fin n))) := by
        conv_lhs => rw [← Finset.insert_erase hm]
        rw [Finset.biUnion_insert]
      rcases node_cases C S m (vt C S m) with ⟨_, htrue⟩ | ⟨_, hsmall, _⟩ | ⟨hpriv, g, hg, hnode⟩
      · have : v C S m = true := htrue
        rw [this] at hvm
        exact absurd hvm (by simp)
      · rw [hsplit]
        have h1 := Finset.card_union_le (A C m : Finset (Fin n))
          ((R.erase m).biUnion (fun w => (A C w : Finset (Fin n))))
        have h2 := ih (R.erase m) hR0
        have h3 := pc_succ_le C S m
        omega
      · obtain ⟨hnm, hlt⟩ := priv_is_gate C S m hpriv
        have hmn : n + (m - n) = m := by omega
        obtain ⟨hop, a, b, hin⟩ := gate_shape C hC (m - n) g hg
        have hval : g.op.eval (g.inputs.map (vt C S m)) = false := by
          rw [← hnode]
          exact hvm
        have hpcs := pc_succ_priv C S m hpriv
        rcases hop with hop | hop
        · rw [hop, hin] at hval
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            Bool.and_true, id_eq, Bool.and_eq_false_iff] at hval
          have hAeq := A_and (n := n) C (m - n) a b g hg hop hin
          rw [hmn] at hAeq
          have hne : (A C m : Finset (Fin n)).Nonempty := by
            rw [← Finset.card_pos]
            have := hpriv.2
            omega
          have hone : ∃ c : ℕ, vt C S m c = false ∧ c < m ∧
              (A C m : Finset (Fin n)) ⊆ A C c := by
            obtain ⟨p, hp⟩ := hne
            rw [hAeq, Finset.mem_inter] at hp
            have hsub : ∀ c : ℕ, p ∈ chA C m c → c < m ∧ (chA C m c : Finset (Fin n)) = A C c := by
              intro c hc
              unfold chA at hc ⊢
              by_cases hlt' : c < m
              · exact ⟨hlt', by simp [hlt']⟩
              · simp [hlt'] at hc
            rcases hval with ha | hb
            · obtain ⟨h1, h2⟩ := hsub a hp.1
              refine ⟨a, ha, h1, ?_⟩
              rw [hAeq, ← h2]
              exact Finset.inter_subset_left
            · obtain ⟨h1, h2⟩ := hsub b hp.2
              refine ⟨b, hb, h1, ?_⟩
              rw [hAeq, ← h2]
              exact Finset.inter_subset_right
          obtain ⟨c, hcv, hclt, hcsub⟩ := hone
          have hcv' : v C S c = false := by rw [← vt_lt C S m c hclt]; exact hcv
          have hR' : ∀ w ∈ insert c (R.erase m), w < m ∧ v C S w = false := by
            intro w hw
            rw [Finset.mem_insert] at hw
            rcases hw with rfl | hw
            · exact ⟨hclt, hcv'⟩
            · exact hR0 w hw
          have hle : R.biUnion (fun w => (A C w : Finset (Fin n))) ⊆
              (insert c (R.erase m)).biUnion (fun w => (A C w : Finset (Fin n))) := by
            rw [hsplit, Finset.biUnion_insert]
            exact Finset.union_subset_union hcsub (Finset.Subset.refl _)
          have h1 := Finset.card_le_card hle
          have h2 := ih _ hR'
          have h3 : (insert c (R.erase m)).card ≤ (R.erase m).card + 1 :=
            Finset.card_insert_le c (R.erase m)
          omega
        · rw [hop, hin] at hval
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            Bool.or_false, id_eq, Bool.or_eq_false_iff] at hval
          obtain ⟨ha, hb⟩ := hval
          have hAeq := A_or (n := n) C (m - n) a b g hg hop hin
          rw [hmn] at hAeq
          let R' : Finset ℕ := (R.erase m) ∪ ((({a, b} : Finset ℕ)).filter (fun c => c < m))
          have hR' : ∀ w ∈ R', w < m ∧ v C S w = false := by
            intro w hw
            rw [Finset.mem_union, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with hw | ⟨hw, hwlt⟩
            · exact hR0 w hw
            · refine ⟨hwlt, ?_⟩
              rw [← vt_lt C S m w hwlt]
              rcases hw with rfl | rfl
              · exact ha
              · exact hb
          have hch : ∀ c : ℕ, (c = a ∨ c = b) → (chA C m c : Finset (Fin n)) ⊆
              R'.biUnion (fun w => (A C w : Finset (Fin n))) := by
            intro c hc
            unfold chA
            by_cases hlt' : c < m
            · simp only [hlt', ite_true]
              apply Finset.subset_biUnion_of_mem (fun w => (A C w : Finset (Fin n)))
              rw [Finset.mem_union, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨hc, hlt'⟩
            · simp [hlt']
          have hle : R.biUnion (fun w => (A C w : Finset (Fin n))) ⊆
              R'.biUnion (fun w => (A C w : Finset (Fin n))) := by
            rw [hsplit, hAeq]
            apply Finset.union_subset
            · exact Finset.union_subset (hch a (Or.inl rfl)) (hch b (Or.inr rfl))
            · exact Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_left
          have h1 := Finset.card_le_card hle
          have h2 := ih R' hR'
          have h3 : R'.card ≤ (R.erase m).card + 2 := by
            have h4 : R'.card ≤ (R.erase m).card +
                ((({a, b} : Finset ℕ)).filter (fun c => c < m)).card :=
              Finset.card_union_le (R.erase m) ((({a, b} : Finset ℕ)).filter (fun c => c < m))
            have h5 : ((({a, b} : Finset ℕ)).filter (fun c => c < m)).card ≤ 2 := by
              have h6 := Finset.card_filter_le ({a, b} : Finset ℕ) (fun c => c < m)
              have h7 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_le_two
              omega
            omega
          omega
    · have hR0 : ∀ w ∈ R, w < m ∧ v C S w = false := by
        intro w hw
        have hne : w ≠ m := fun h => hm (h ▸ hw)
        have hw' := hR w hw
        exact ⟨by omega, hw'.2⟩
      have h1 := ih R hR0
      have h2 := pc_succ_le C S m
      omega

lemma main (n k c o : ℕ) (S : Finset (Fin n)) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hS : ∀ p : Fin n,
      (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD o false = true ↔ p ∈ S)
    (hk : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD o false = false)
    (hck : c ≤ k) (hcS : c + 1 ≤ S.card) :
    c ≤ ((Finset.range C.size).filter (fun j =>
      (Finset.univ.filter (fun p : Fin n =>
        (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧
      2 ≤ (Finset.univ.filter (fun p : Fin n =>
        (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card)).card := by
  classical
  have hGood : Good C := hC
  have hcount := pc_le_count C S (o + 1)
  have hAo : (A C o : Finset (Fin n)) = S := by
    ext p
    rw [mem_A]
    exact hS p
  have hfin : c ≤ pc C S (o + 1) := by
    cases hv : v C S o with
    | true =>
      obtain ⟨Y, hd, hwY, hcY⟩ := lemA C hGood S (o + 1) {o} (by
        intro w hw
        rw [Finset.mem_singleton] at hw
        rw [hw]
        exact ⟨Nat.lt_succ_self _, hv⟩)
      have hWo : W C (ind Y) o = true := hwY o (Finset.mem_singleton_self o)
      have hfilter : (Finset.univ.filter (fun q : Fin n => ind Y q = true)) = Y := by
        ext q
        simp [ind]
      have hgt : k < Y.card := by
        by_contra hle
        have hfalse := hk (ind Y) (by rw [hfilter]; omega) (by
          intro q hq
          simp only [ind, decide_eq_false_iff_not]
          exact fun hqY => (Finset.disjoint_left.mp hd hqY) hq)
        have : W C (ind Y) o = false := hfalse
        rw [this] at hWo
        exact absurd hWo (by simp)
      rw [Finset.card_singleton] at hcY
      omega
    | false =>
      have hB := lemB C hGood S (o + 1) {o} (by
        intro w hw
        rw [Finset.mem_singleton] at hw
        rw [hw]
        exact ⟨Nat.lt_succ_self _, hv⟩)
      rw [Finset.singleton_biUnion, hAo, Finset.card_singleton] at hB
      omega
  exact le_trans hfin hcount

end PEqualNP.Outside.L_meta_278

theorem PEqualNP.Outside.L_meta_278 : ∀ (n k c o : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD o false = true ↔ p ∈ S) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD o false = false) → c ≤ k → c + 1 ≤ S.card → c ≤ ((Finset.range C.size).filter (fun j => (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card)).card :=
  PEqualNP.Outside.L_meta_278.main
