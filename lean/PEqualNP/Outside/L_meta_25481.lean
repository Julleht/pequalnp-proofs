import Mathlib
import PEqualNP.Defs

-- L-meta-25481: let S be the wires reachable from u along gate edges avoiding O. Strong induction on the wire index shows
-- every wire outside S (and O itself) that is on at 1_uc is on at 1_vc: inputs other than u agree, O is on at 1_vc by
-- hypothesis, and an AND/OR gate outside S reads only wires outside S or O, so monotonicity passes the property up.
-- The output is outside S, so G u c -> G v c. Wire-evaluation lemmas (fold_len .. oneEach_get) copied from merged L_meta_17164.

namespace PEqualNP.Outside.L_meta_25481_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dg : Gate := ⟨GateOp.or, []⟩

lemma fold_len (gs : List Gate) (x : List Bool) :
    (gs.foldl wstep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [wstep]
    omega

lemma getD_app_left (x : List Bool) (v : Bool) (i : ℕ) (hi : i < x.length) :
    (x ++ [v]).getD i false = x.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma fold_low (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl wstep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (wstep x g) (by simp [wstep]; omega)]
    exact getD_app_left x _ i hi

lemma fold_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hin : ∀ i ∈ (gs.getD j dg).inputs, i < x.length + j) :
    (gs.foldl wstep x).getD (x.length + j) false =
      (gs.getD j dg).op.eval ((gs.getD j dg).inputs.map fun i => (gs.foldl wstep x).getD i false) := by
  induction gs generalizing x j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have hg : (g :: gs).getD 0 dg = g := rfl
      rw [hg] at hin ⊢
      rw [Nat.add_zero, fold_low gs (wstep x g) x.length (by simp [wstep])]
      have h1 : (wstep x g).getD x.length false =
          g.op.eval (g.inputs.map fun i => x.getD i false) := by
        simp [wstep, List.getD_eq_getElem?_getD]
      rw [h1]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi' := hin i hi
      rw [fold_low gs (wstep x g) i (by simp [wstep]; omega)]
      exact (getD_app_left x _ i (by omega)).symm
    | succ j =>
      have hg : (g :: gs).getD (j + 1) dg = gs.getD j dg := rfl
      rw [hg] at hin ⊢
      have hl : (wstep x g).length = x.length + 1 := by simp [wstep]
      have := ih (wstep x g) j (by simpa using hj) (by intro i hi; have := hin i hi; omega)
      rw [hl] at this
      rw [show x.length + (j + 1) = x.length + 1 + j by omega]
      exact this

def val (C : Circuit) (x : List Bool) (w : ℕ) : Bool := (C.wires x).getD w false

lemma val_input (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    val C x w = x.getD w false :=
  fold_low C.gates x w hw

lemma val_high (C : Circuit) (x : List Bool) (w : ℕ) (hw : x.length + C.gates.length ≤ w) :
    val C x w = false := by
  unfold val
  have hl : (C.wires x).length = x.length + C.gates.length := fold_len C.gates x
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (C.wires x).length ≤ w by omega)]

def GatesOk (N : ℕ) (C : Circuit) : Prop :=
  Monotone2 C ∧ ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 ∧ (gateAt C j).inputs.Nodup ∧
    ∀ i ∈ (gateAt C j).inputs, i < N + j

lemma oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_get {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ w = u.val ∨ w = n + v.val := by
  unfold oneEach
  by_cases hw : w < n
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hw)]
    simp [hw, Fin.ext_iff]
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using hw)]
    by_cases hw2 : w - n < m
    · simp [hw2, Fin.ext_iff]
      omega
    · simp [hw2]
      omega

lemma val_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hin : ∀ i ∈ (gateAt C j).inputs, i < x.length + j) :
    val C x (x.length + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (val C x)) :=
  fold_val C.gates x j hj hin

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (f g : ℕ → Bool)
    (h : ∀ i ∈ l, f i = true → g i = true) : op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact h i hi (H _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨g i, ⟨i, hi, rfl⟩, h i hi hb⟩

theorem main {n m : ℕ} (C : Circuit) (u v : Fin n) (c : Fin m) (O : ℕ)
    (hmono : Monotone2 C) (hrb : ReadsBack (n + m) C)
    (hO : val C (oneEach v c) O = true)
    (reach : ℕ → Prop) (hu : reach u.val)
    (hcl : ∀ j < C.gates.length, ∀ a ∈ (gateAt C j).inputs, a ≠ O → n + m + j ≠ O → reach a →
      reach (n + m + j)) :
    ∀ w, (¬ reach w ∨ w = O) → val C (oneEach u c) w = true → val C (oneEach v c) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hv
    by_cases hwO : w = O
    · subst hwO; exact hO
    have hw' : ¬ reach w := hw.resolve_right hwO
    by_cases hwN : w < n + m
    · rw [val_input C _ w (by rw [oneEach_len]; exact hwN)] at hv
      rw [val_input C _ w (by rw [oneEach_len]; exact hwN)]
      rw [oneEach_get] at hv ⊢
      rcases hv with h | h
      · exact absurd (h ▸ hu) hw'
      · exact Or.inr h
    by_cases hwG : w < n + m + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + m + j := ⟨w - (n + m), by omega⟩
      have hj : j < C.gates.length := by omega
      have ex := val_gate C (oneEach u c) j hj (by intro i hi; rw [oneEach_len]; exact hrb j hj i hi)
      have ey := val_gate C (oneEach v c) j hj (by intro i hi; rw [oneEach_len]; exact hrb j hj i hi)
      rw [oneEach_len] at ex ey
      rw [ex] at hv
      rw [ey]
      have hmem : gateAt C j ∈ C.gates := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      have hop := (hmono _ hmem).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      refine eval_mono _ hop _ _ _ ?_ hv
      intro a ha hfa
      have hlt : a < n + m + j := hrb j hj a ha
      refine ih a hlt ?_ hfa
      by_cases haO : a = O
      · exact Or.inr haO
      · exact Or.inl fun hra => hw' (hcl j hj a ha haO hwO hra)
    · rw [val_high C _ w (by rw [oneEach_len]; omega)] at hv
      exact absurd hv (by simp)

end PEqualNP.Outside.L_meta_25481_aux

theorem PEqualNP.Outside.L_meta_25481 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (u v : Fin n) (O : ℕ),
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  u ≠ v →
  PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) u.val = 1 →
  C.output ≠ u.val →
  O < n + m + C.gates.length →
  (∀ c : Fin m, (C.wires (PEqualNP.Represents.oneEach v c)).getD O false = true) →
  (¬ Relation.TransGen
    (fun a b : ℕ => a ≠ O ∧ b ≠ O ∧
      ∃ j : Fin C.gates.length, b = n + m + j.val ∧
        a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).inputs)
    u.val C.output) →
  ∀ c : Fin m, G u c = true → G v c = true := by
  open PEqualNP.Outside.L_meta_25481_aux in
  intro n m G C u v O hmono hrb hrep _huv _hread hout _hOlt hOn hnp c hGu
  rw [← hrep u c] at hGu
  rw [← hrep v c]
  refine main C u v c O hmono hrb (hOn c)
    (fun w => w = u.val ∨ Relation.TransGen
      (fun a b : ℕ => a ≠ O ∧ b ≠ O ∧
        ∃ j : Fin C.gates.length, b = n + m + j.val ∧
          a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).inputs) u.val w)
    (Or.inl rfl) ?_ C.output ?_ hGu
  · intro j hj a ha haO hkO hra
    right
    rcases hra with rfl | ht
    · exact Relation.TransGen.single ⟨haO, hkO, ⟨j, hj⟩, rfl, ha⟩
    · exact ht.tail ⟨haO, hkO, ⟨j, hj⟩, rfl, ha⟩
  · left
    rintro (h | h)
    · exact hout h
    · exact hnp h
