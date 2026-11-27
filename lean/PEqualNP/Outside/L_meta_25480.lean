import Mathlib
import PEqualNP.Defs

-- L-meta-25480: descent from the output wire along wires that are true at 1_uv but false at both the row-only and the
-- column-only input. Monotonicity makes the output such a wire (row-only <= 1_uc, column-only <= 1_rv); an OR gate passes the
-- property to an operand, and an AND gate either passes it to an operand or has operands split row-only/col-only.
-- Strong induction on the wire index. Wire-evaluation lemmas (fold_len .. val_or) copied from merged L_meta_17164.

namespace PEqualNP.Outside.L_meta_25480_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents PEqualNP.EdgeOwnership

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

lemma gate_form {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 N C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ p q, (gateAt C j).inputs = [p, q] ∧ p < N + j ∧ q < N + j ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  obtain ⟨hao, hrb, hlen⟩ := h
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hop := hao _ hmem
  have hl := hlen _ hmem
  have hlt := hrb j hj
  match hi : (gateAt C j).inputs, hl with
  | [p, q], _ =>
    rw [hi] at hlt
    exact ⟨p, q, rfl, hlt p (by simp), hlt q (by simp), hop⟩

lemma val_and {N : ℕ} {C : Circuit} (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) (p q : ℕ) (hi : (gateAt C j).inputs = [p, q]) (hp : p < N + j)
    (hq : q < N + j) (hop : (gateAt C j).op = GateOp.and) :
    val C x (N + j) = (val C x p && val C x q) := by
  have h := fold_val C.gates x j hj (by
    intro i hi'
    have : (C.gates.getD j dg).inputs = [p, q] := hi
    rw [this] at hi'
    simp at hi'
    rcases hi' with rfl | rfl <;> omega)
  have e1 : (C.gates.getD j dg).inputs = [p, q] := hi
  have e2 : (C.gates.getD j dg).op = GateOp.and := hop
  rw [e1, e2, hx] at h
  unfold val
  rw [show C.wires x = C.gates.foldl wstep x from rfl, h]
  simp [GateOp.eval]

lemma val_or {N : ℕ} {C : Circuit} (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) (p q : ℕ) (hi : (gateAt C j).inputs = [p, q]) (hp : p < N + j)
    (hq : q < N + j) (hop : (gateAt C j).op = GateOp.or) :
    val C x (N + j) = (val C x p || val C x q) := by
  have h := fold_val C.gates x j hj (by
    intro i hi'
    have : (C.gates.getD j dg).inputs = [p, q] := hi
    rw [this] at hi'
    simp at hi'
    rcases hi' with rfl | rfl <;> omega)
  have e1 : (C.gates.getD j dg).inputs = [p, q] := hi
  have e2 : (C.gates.getD j dg).op = GateOp.or := hop
  rw [e1, e2, hx] at h
  unfold val
  rw [show C.wires x = C.gates.foldl wstep x from rfl, h]
  simp [GateOp.eval]

lemma mono {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 N C) (x x' : List Bool)
    (hx : x.length = N) (hx' : x'.length = N)
    (hin : ∀ w < N, x.getD w false = true → x'.getD w false = true) :
    ∀ w, val C x w = true → val C x' w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hwN : w < N
    · rw [val_input C x w (by omega)] at hv
      rw [val_input C x' w (by omega)]
      exact hin w hwN hv
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      by_cases hj : j < C.gates.length
      · obtain ⟨p, q, hi, hp, hq, hop⟩ := gate_form h j hj
        rcases hop with hop | hop
        · rw [val_and x hx j hj p q hi hp hq hop, Bool.and_eq_true] at hv
          rw [val_and x' hx' j hj p q hi hp hq hop, Bool.and_eq_true]
          exact ⟨ih p hp hv.1, ih q hq hv.2⟩
        · rw [val_or x hx j hj p q hi hp hq hop, Bool.or_eq_true] at hv
          rw [val_or x' hx' j hj p q hi hp hq hop, Bool.or_eq_true]
          exact hv.imp (ih p hp) (ih q hq)
      · rw [val_high C x (N + j) (by omega)] at hv
        cases hv

def Split (C : Circuit) (r c : List Bool) (a b : ℕ) : Prop :=
  val C r a = true ∧ val C r b = false ∧ val C c b = true ∧ val C c a = false

lemma split_cases (a1 a2 a3 a4 : Bool) (hr : (a1 && a3) = false) (hc : (a2 && a4) = false)
    (hp : ¬ (a1 = false ∧ a2 = false)) (hq : ¬ (a3 = false ∧ a4 = false)) :
    (a1 = true ∧ a3 = false ∧ a4 = true ∧ a2 = false) ∨
      (a3 = true ∧ a1 = false ∧ a2 = true ∧ a4 = false) := by
  revert hr hc hp hq
  cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> decide

lemma descent {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 N C) (x r c : List Bool)
    (hx : x.length = N) (hr : r.length = N) (hc : c.length = N)
    (hin : ∀ w < N, x.getD w false = true → r.getD w false = true ∨ c.getD w false = true) :
    ∀ w, val C x w = true → val C r w = false → val C c w = false →
      ∃ j, ∃ _ : j < C.gates.length, ∃ a b, (gateAt C j).op = GateOp.and ∧
        (gateAt C j).inputs = [a, b] ∧ val C x (N + j) = true ∧
        (Split C r c a b ∨ Split C r c b a) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hvr hvc
    by_cases hwN : w < N
    · rw [val_input C x w (by omega)] at hv
      rw [val_input C r w (by omega)] at hvr
      rw [val_input C c w (by omega)] at hvc
      rcases hin w hwN hv with h1 | h1
      · rw [h1] at hvr; cases hvr
      · rw [h1] at hvc; cases hvc
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      by_cases hj : j < C.gates.length
      · obtain ⟨p, q, hi, hp, hq, hop⟩ := gate_form h j hj
        rcases hop with hop | hop
        · have hv' := hv
          rw [val_and x hx j hj p q hi hp hq hop, Bool.and_eq_true] at hv'
          rw [val_and r hr j hj p q hi hp hq hop] at hvr
          rw [val_and c hc j hj p q hi hp hq hop] at hvc
          obtain ⟨hxp, hxq⟩ := hv'
          by_cases hp0 : val C r p = false ∧ val C c p = false
          · exact ih p hp hxp hp0.1 hp0.2
          by_cases hq0 : val C r q = false ∧ val C c q = false
          · exact ih q hq hxq hq0.1 hq0.2
          refine ⟨j, hj, p, q, hop, hi, hv, ?_⟩
          exact split_cases _ _ _ _ hvr hvc hp0 hq0
        · rw [val_or x hx j hj p q hi hp hq hop, Bool.or_eq_true] at hv
          rw [val_or r hr j hj p q hi hp hq hop, Bool.or_eq_false_iff] at hvr
          rw [val_or c hc j hj p q hi hp hq hop, Bool.or_eq_false_iff] at hvc
          rcases hv with hv | hv
          · exact ih p hp hv hvr.1 hvc.1
          · exact ih q hq hv hvr.2 hvc.2
      · rw [val_high C x (N + j) (by omega)] at hv
        cases hv

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

lemma row_get {n m : ℕ} (u : Fin n) (w : ℕ) :
    (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false).getD w false = true ↔
      w = u.val := by
  by_cases hw : w < n
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hw)]
    simp [hw, Fin.ext_iff]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using hw)]
    rw [List.getElem?_replicate]
    constructor
    · intro h
      split_ifs at h <;> simp at h
    · intro h
      simp at hw
      omega

lemma col_get {n m : ℕ} (v : Fin m) (w : ℕ) :
    (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v))).getD w false = true ↔
      w = n + v.val := by
  by_cases hw : w < n
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hw)]
    simp [hw]
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using hw)]
    by_cases hw2 : w - n < m
    · simp [hw2, Fin.ext_iff]
      omega
    · simp [hw2]
      omega

end PEqualNP.Outside.L_meta_25480_aux

open PEqualNP.Outside.L_meta_25480_aux PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_25480 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.IsAO2 (n + m) C →
  PEqualNP.Represents.Represents G C →
  ∀ (u : Fin n) (v : Fin m), G u v = true →
    (∃ c : Fin m, G u c = false) → (∃ r : Fin n, G r v = false) →
    let rowOnly := List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false
    let colOnly := List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v))
    let value := fun (x : List Bool) (w : ℕ) => (C.wires x).getD w false
    let split := fun (left right : ℕ) =>
      value rowOnly left = true ∧ value rowOnly right = false ∧
      value colOnly right = true ∧ value colOnly left = false
    ∃ (j : Fin C.gates.length) (a b : ℕ),
      (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      (C.gates.get j).inputs = [a, b] ∧
      value (PEqualNP.Represents.oneEach u v) (n + m + j.val) = true ∧
      (split a b ∨ split b a) := by
  intro n m G C hC hrep u v huv hc hr R K value sp
  obtain ⟨c0, hc0⟩ := hc
  obtain ⟨r0, hr0⟩ := hr
  have hlx := oneEach_len u v
  have hlr : R.length = n + m := by simp [R]
  have hlc : K.length = n + m := by simp [K]
  have hout : val C (oneEach u v) C.output = true := by
    rw [← huv, ← hrep u v]; rfl
  have hrow : val C R C.output = false := by
    cases h : val C R C.output
    · rfl
    · have h2 := mono hC R (oneEach u c0) hlr (oneEach_len u c0) (by
        intro w _ hw
        rw [oneEach_get]
        exact Or.inl ((row_get (m := m) u w).1 hw)) C.output h
      have e : val C (oneEach u c0) C.output = G u c0 := hrep u c0
      rw [e, hc0] at h2
      cases h2
  have hcol : val C K C.output = false := by
    cases h : val C K C.output
    · rfl
    · have h2 := mono hC K (oneEach r0 v) hlc (oneEach_len r0 v) (by
        intro w _ hw
        rw [oneEach_get]
        exact Or.inr ((col_get (n := n) v w).1 hw)) C.output h
      have e : val C (oneEach r0 v) C.output = G r0 v := hrep r0 v
      rw [e, hr0] at h2
      cases h2
  have hin : ∀ w < n + m, (oneEach u v).getD w false = true →
      R.getD w false = true ∨ K.getD w false = true := by
    intro w _ hw
    rcases (oneEach_get u v w).1 hw with h1 | h1
    · exact Or.inl ((row_get (m := m) u w).2 h1)
    · exact Or.inr ((col_get (n := n) v w).2 h1)
  obtain ⟨j, hj, a, b, hop, hi, hv, hs⟩ :=
    descent hC (oneEach u v) R K hlx hlr hlc hin C.output hout hrow hcol
  have hg : C.gates.get ⟨j, hj⟩ = gateAt C j := by
    simp [gateAt, List.getElem?_eq_getElem hj]
  refine ⟨⟨j, hj⟩, a, b, hg ▸ hop, hg ▸ hi, hv, ?_⟩
  exact hs
