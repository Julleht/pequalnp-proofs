import Mathlib
import PEqualNP.Defs

-- L-meta-25487: compare the column-only input with the input that also turns on one row. Wires the changed row cannot reach
-- (around a blocked wire whose two values agree) keep their value, by strong induction on the wire index.
-- Row u: an off operand switches the AND off and freezes the output; row v: monotonicity lifts an on operand.
-- Wire-evaluation lemmas (fold_len .. val_high, oneEach_get, col_get) copied from merged L_meta_17164 and L-meta-25480.

namespace PEqualNP.Outside.L_meta_25487_aux

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

lemma val_gate {N : ℕ} {C : Circuit} (hrb : ReadsBack N C) (x : List Bool) (hx : x.length = N)
    (j : ℕ) (hj : j < C.gates.length) :
    val C x (N + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (val C x)) := by
  have h := fold_val C.gates x j hj (by rw [hx]; exact hrb j hj)
  rw [hx] at h
  unfold val
  rw [show C.wires x = C.gates.foldl wstep x from rfl]
  exact h

lemma gate_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma mono {N : ℕ} {C : Circuit} (hm : Monotone2 C) (hrb : ReadsBack N C) (x x' : List Bool)
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
      · rw [val_gate hrb x hx j hj] at hv
        rw [val_gate hrb x' hx' j hj]
        have hop := (hm _ (gate_mem C j hj)).1
        have hlt := hrb j hj
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · rw [hop] at hv ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hv ⊢
          rintro _ ⟨i, hi, rfl⟩
          exact ih i (hlt i hi) (hv _ ⟨i, hi, rfl⟩)
        · rw [hop] at hv ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hv ⊢
          obtain ⟨_, ⟨i, hi, rfl⟩, h⟩ := hv
          exact ⟨_, ⟨i, hi, rfl⟩, ih i (hlt i hi) h⟩
      · rw [val_high C x (N + j) (by omega)] at hv
        cases hv

lemma agree {N : ℕ} {C : Circuit} (hrb : ReadsBack N C) (x y : List Bool) (hx : x.length = N)
    (hy : y.length = N) (u z : ℕ)
    (hxy : ∀ w < N, w ≠ u → x.getD w false = y.getD w false) (hz : val C x z = val C y z) :
    ∀ w, (w = z ∨ ¬ Relation.ReflTransGen (fun prev next : ℕ => prev ≠ z ∧ next ≠ z ∧
        ∃ idx : Fin C.gates.length, next = N + idx.val ∧ prev ∈ (gateAt C idx.val).inputs) u w) →
      val C x w = val C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwz : w = z
    · rw [hwz]; exact hz
    have hnr := hw.resolve_left hwz
    by_cases hwN : w < N
    · have hwu : w ≠ u := by
        rintro rfl
        exact hnr Relation.ReflTransGen.refl
      rw [val_input C x w (by omega), val_input C y w (by omega)]
      exact hxy w hwN hwu
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      by_cases hj : j < C.gates.length
      · rw [val_gate hrb x hx j hj, val_gate hrb y hy j hj]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hlt := hrb j hj i hi
        apply ih i hlt
        by_cases hiz : i = z
        · exact Or.inl hiz
        · exact Or.inr fun hr => hnr (hr.tail ⟨hiz, hwz, ⟨j, hj⟩, rfl, hi⟩)
      · rw [val_high C x (N + j) (by omega), val_high C y (N + j) (by omega)]

lemma rtg_weaken {r p : ℕ → ℕ → Prop} (h : ∀ a b, r a b → p a b) {a b : ℕ}
    (hr : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

lemma col_eq {n m : ℕ} (r : Fin n) (c : Fin m) (w : ℕ) (hw : w ≠ r.val) :
    (oneEach r c).getD w false =
      (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))).getD w false := by
  rw [Bool.eq_iff_iff, oneEach_get, col_get]
  constructor
  · rintro (h | h)
    · exact absurd h hw
    · exact h
  · exact Or.inr

lemma col_le {n m : ℕ} (r : Fin n) (c : Fin m) (w : ℕ) :
    (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))).getD w false = true →
      (oneEach r c).getD w false = true := by
  rw [oneEach_get, col_get]
  exact Or.inr

lemma col_len (n m : ℕ) (c : Fin m) :
    (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))).length = n + m := by
  simp

end PEqualNP.Outside.L_meta_25487_aux

open PEqualNP.Outside.L_meta_25487_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_25487 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n)
    (j : Fin C.gates.length) (q : ℕ),
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let g := n + m + j.val
  let edge := fun source target : ℕ => ∃ idx : Fin C.gates.length,
    target = n + m + idx.val ∧ source ∈ (gate idx.val).inputs
  let cuts := fun (z start : ℕ) =>
    ¬ (start ≠ z ∧ C.output ≠ z ∧ Relation.ReflTransGen
      (fun prev next : ℕ => prev ≠ z ∧ next ≠ z ∧ edge prev next) start C.output)
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C → u ≠ v →
  (gate j.val).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  q ∈ (gate j.val).inputs →
  cuts g u.val → cuts q v.val → ¬ Relation.ReflTransGen edge u.val q →
  ∀ c : Fin m, (∃ w : Fin n, G w c = false) →
    let col := List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))
    let value := (C.wires col).getD q false
    (G u c = true → value = true) ∧ (G v c = true → value = false) := by
  intro n m G C u v j q gate g edge cuts hmono hrb hrep _huv hand hq hcutg hcutq hnr c hc col value
  have hK : col.length = n + m := col_len n m c
  obtain ⟨w0, hw0⟩ := hc
  have hKout : val C col C.output = false := by
    cases h : val C col C.output
    · rfl
    · have h2 := mono hmono hrb col (oneEach w0 c) hK (oneEach_len w0 c)
        (fun w _ hw => col_le w0 c w hw) C.output h
      have e : val C (oneEach w0 c) C.output = G w0 c := hrep w0 c
      rw [e, hw0] at h2
      cases h2
  have hqv : value = val C col q := rfl
  rw [hqv]
  constructor
  · intro hu
    have hout : val C (oneEach u c) C.output = true := by
      have e : val C (oneEach u c) C.output = G u c := hrep u c
      rw [e, hu]
    cases hval : val C col q
    · exfalso
      have hxy : ∀ w < n + m, w ≠ u.val → (oneEach u c).getD w false = col.getD w false :=
        fun w _ hw => col_eq u c w hw
      have hqq : val C (oneEach u c) q = val C col q := by
        refine agree hrb (oneEach u c) col (oneEach_len u c) hK u.val (n + m + C.gates.length)
          hxy ?_ q (Or.inr fun hr => hnr (rtg_weaken (p := edge) (fun _ _ h => h.2.2) hr))
        rw [val_high C _ _ (by rw [oneEach_len]), val_high C _ _ (by rw [hK])]
      have hgK : val C col g = false := by
        rw [val_gate hrb col hK j.val j.isLt, hand]
        simp only [GateOp.eval, List.all_eq_false, List.mem_map, id]
        exact ⟨_, ⟨q, hq, rfl⟩, by rw [hval]; decide⟩
      have hgx : val C (oneEach u c) g = false := by
        rw [val_gate hrb (oneEach u c) (oneEach_len u c) j.val j.isLt, hand]
        simp only [GateOp.eval, List.all_eq_false, List.mem_map, id]
        exact ⟨_, ⟨q, hq, rfl⟩, by rw [hqq, hval]; decide⟩
      have ho : val C (oneEach u c) C.output = val C col C.output := by
        refine agree hrb (oneEach u c) col (oneEach_len u c) hK u.val g hxy (by rw [hgx, hgK])
          C.output ?_
        by_cases hog : C.output = g
        · exact Or.inl hog
        · exact Or.inr fun hr => hcutg ⟨by omega, hog, hr⟩
      rw [hout, hKout] at ho
      cases ho
    · rfl
  · intro hv
    have hout : val C (oneEach v c) C.output = true := by
      have e : val C (oneEach v c) C.output = G v c := hrep v c
      rw [e, hv]
    cases hval : val C col q
    · rfl
    · exfalso
      have hxy : ∀ w < n + m, w ≠ v.val → (oneEach v c).getD w false = col.getD w false :=
        fun w _ hw => col_eq v c w hw
      have hyq : val C (oneEach v c) q = true :=
        mono hmono hrb col (oneEach v c) hK (oneEach_len v c)
          (fun w _ hw => col_le v c w hw) q hval
      have ho : val C (oneEach v c) C.output = val C col C.output := by
        refine agree hrb (oneEach v c) col (oneEach_len v c) hK v.val q hxy (by rw [hyq, hval])
          C.output ?_
        by_cases hoq : C.output = q
        · exact Or.inl hoq
        · by_cases hvq : v.val = q
          · exfalso
            rw [← hvq, val_input C col v.val (by rw [hK]; omega)] at hval
            have := (col_get (n := n) c v.val).1 hval
            omega
          · exact Or.inr fun hr => hcutq ⟨hvq, hoq, hr⟩
      rw [hout, hKout] at ho
      cases ho
