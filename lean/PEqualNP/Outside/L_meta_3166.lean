import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3166
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- the same gate with its wire numbers renamed
def mapGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

theorem fold_len (gs : List Gate) : ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih => intro w; simp only [List.foldl_cons, ih, List.length_cons]; simp [step]; omega

theorem fold_getD (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by unfold step; simp; omega)]
    unfold step
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem ofFn_getD (a : Fin 9 → Bool) (i : ℕ) :
    (List.ofFn a).getD i false = if h : i < 9 then a ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> rfl

theorem snoc_getD_len (l : List Bool) (v : Bool) (n : ℕ) (h : n = l.length) :
    (l ++ [v]).getD n false = v := by
  subst h
  simp [List.getD_eq_getElem?_getD]

-- One phase of a renaming: while the gates read only wires already related (and never `bad`), and the
-- wires they create are renamed by the shift `c`, the old run W and the renamed run N stay related.
theorem phase (ρ : ℕ → ℕ) (c bad : ℕ) : ∀ (gs : List Gate) (W N : List Bool),
    N.length + c = W.length →
    (∀ i, W.length ≤ i → i < W.length + gs.length → ρ i = i - c) →
    (∀ i, i < W.length → i ≠ bad → ρ i < N.length ∧ W.getD i false = N.getD (ρ i) false) →
    (∀ j (hj : j < gs.length), ∀ a ∈ (gs[j]).inputs, a < W.length + j ∧ a ≠ bad) →
    ((gs.map (mapGate ρ)).foldl step N).length + c = (gs.foldl step W).length ∧
    ∀ i, i < (gs.foldl step W).length → i ≠ bad →
      ρ i < ((gs.map (mapGate ρ)).foldl step N).length ∧
      (gs.foldl step W).getD i false = ((gs.map (mapGate ρ)).foldl step N).getD (ρ i) false := by
  intro gs
  induction gs with
  | nil => intro W N hl _ hinv _; exact ⟨hl, hinv⟩
  | cons g gs ih =>
    intro W N hl hfut hinv hrd
    simp only [List.map_cons, List.foldl_cons]
    have hg := hrd 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hg
    have hval : (mapGate ρ g).op.eval ((mapGate ρ g).inputs.map fun i => N.getD i false) =
        g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ((hinv a (hg a ha).1 (hg a ha).2).2).symm
    have hWl : (step W g).length = W.length + 1 := by simp [step]
    have hNl : (step N (mapGate ρ g)).length = N.length + 1 := by simp [step]
    apply ih
    · rw [hWl, hNl]; omega
    · intro i hi1 hi2
      rw [hWl] at hi1 hi2
      exact hfut i (by omega) (by simp only [List.length_cons]; omega)
    · intro i hi hb
      rw [hWl] at hi
      rw [hNl]
      by_cases hiW : i < W.length
      · obtain ⟨h1, h2⟩ := hinv i hiW hb
        refine ⟨by omega, ?_⟩
        unfold step
        rw [List.getD_append _ _ _ _ hiW, List.getD_append _ _ _ _ h1]
        exact h2
      · have hiE : i = W.length := by omega
        have hρ : ρ i = N.length := by
          rw [hfut i (by omega) (by simp only [List.length_cons]; omega)]; omega
        refine ⟨by omega, ?_⟩
        rw [hρ, hiE]
        unfold step
        rw [snoc_getD_len _ _ _ rfl, snoc_getD_len _ _ _ rfl]
        exact hval.symm
    · intro j hj a ha
      have h := hrd (j + 1) (by simpa using hj) a (by simpa using ha)
      rw [hWl]
      exact ⟨by omega, h.2⟩

theorem getD_left (A B : List Gate) (d : Gate) (j : ℕ) (hj : j < A.length) :
    (A ++ B).getD j d = A[j] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]

theorem getD_right (A : List Gate) (g : Gate) (B : List Gate) (d : Gate) (j : ℕ) (hj : j < B.length) :
    (A ++ g :: B).getD (A.length + 1 + j) d = B[j] := by
  have h1 : A.length ≤ A.length + 1 + j := by omega
  have h2 : A.length + 1 + j - A.length = j + 1 := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h1, h2, hj]

theorem ab1 (a b : Bool) : (a && b || (a || false)) = a := by cases a <;> cases b <;> rfl
theorem ab2 (a b : Bool) : (a && b || (b || false)) = b := by cases a <;> cases b <;> rfl
theorem ab3 (a b : Bool) : (a || (a && b || false)) = a := by cases a <;> cases b <;> rfl
theorem ab4 (a b : Bool) : (b || (a && b || false)) = b := by cases a <;> cases b <;> rfl

end PEqualNP.Outside.L_meta_3166

theorem PEqualNP.Outside.L_meta_3166 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x2 = (0 : ℕ) ∨ x2 = (2 : ℕ) → PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x1 → x1.output ≠ (9 : ℕ) → List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) x1.gates = [x3] → x3.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3.inputs = [(9 : ℕ), x2] ∨ x3.inputs = [x2, (9 : ℕ)] → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x11 ∧ x11.size + (1 : ℕ) = x1.size ∧ ∀ (x12 : Fin (9 : ℕ) → Bool), x11.eval (List.ofFn x12) = x1.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ))]) := by
  intro C k g hk hf hrb hout hfilt hop hins
  obtain ⟨A, B, hG, hA, hpg, hB⟩ := List.filter_eq_cons_iff.mp hfilt
  have hB' : ∀ b ∈ B, ¬ (9 ∈ b.inputs) := by
    intro b hb
    have := List.filter_eq_nil_iff.mp hB b hb
    simpa using this
  have hA' : ∀ a ∈ A, ¬ (9 ∈ a.inputs) := by
    intro a ha
    simpa using hA a ha
  have hk9 : k < 9 := by rcases hk with rfl | rfl <;> decide
  let ρ : ℕ → ℕ := fun i =>
    if i < 10 + A.length then (if i < 9 then i else i - 1)
    else if i = 10 + A.length then k else i - 2
  refine ⟨⟨A.map (PEqualNP.Outside.L_meta_3166.mapGate ρ) ++ B.map (PEqualNP.Outside.L_meta_3166.mapGate ρ),
    ρ C.output⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_map] at hg'
    rcases hg' with ⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩
    · have := hf h (by rw [hG]; simp [hh])
      simpa [PEqualNP.Outside.L_meta_3166.mapGate] using this
    · have := hf h (by rw [hG]; simp [hh])
      simpa [PEqualNP.Outside.L_meta_3166.mapGate] using this
  · show (A.map _ ++ B.map _).length + 1 = C.gates.length
    rw [hG]; simp; omega
  · intro x
    let inp : List Bool := List.ofFn x ++ [x 0 && x 2]
    have hinpl : inp.length = 10 := by simp [inp]
    -- phase 1: the gates before g
    have ph1 := PEqualNP.Outside.L_meta_3166.phase ρ 1 9 A inp (List.ofFn x) (by simp [inp])
      (by
        intro i h1 h2
        rw [hinpl] at h1 h2
        simp only [ρ]
        rw [if_pos (by omega), if_neg (by omega)])
      (by
        intro i h1 h2
        rw [hinpl] at h1
        have hi9 : i < 9 := by omega
        simp only [ρ]
        rw [if_pos (by omega), if_pos hi9]
        refine ⟨by simpa using hi9, ?_⟩
        simp only [inp]
        rw [List.getD_append _ _ _ _ (by simpa using hi9)])
      (by
        intro j hj a ha
        rw [hinpl]
        have h1 := hrb j (by rw [hG]; simp; omega) a (by
          unfold PEqualNP.MetaComplexity.NestedCover.gateAt
          rw [hG, PEqualNP.Outside.L_meta_3166.getD_left A (g :: B) _ j hj]; exact ha)
        refine ⟨h1, ?_⟩
        intro e
        exact hA' _ (List.getElem_mem hj) (e ▸ ha))
    set W1 := A.foldl PEqualNP.Outside.L_meta_3166.step inp with hW1
    set N1 := (A.map (PEqualNP.Outside.L_meta_3166.mapGate ρ)).foldl PEqualNP.Outside.L_meta_3166.step (List.ofFn x) with hN1
    have hW1l : W1.length = 10 + A.length := by
      rw [hW1, PEqualNP.Outside.L_meta_3166.fold_len, hinpl]
    have hN1l : N1.length = 9 + A.length := by have := ph1.1; omega
    -- the removed gate g is a copy of input k
    have hw9 : W1.getD 9 false = (x 0 && x 2) := by
      rw [hW1, PEqualNP.Outside.L_meta_3166.fold_getD A inp 9 (by rw [hinpl]; decide)]
      exact PEqualNP.Outside.L_meta_3166.snoc_getD_len _ _ 9 (by simp)
    have hwk : W1.getD k false = x ⟨k, hk9⟩ := by
      rw [hW1, PEqualNP.Outside.L_meta_3166.fold_getD A inp k (by rw [hinpl]; omega)]
      simp only [inp]
      rw [List.getD_append _ _ _ _ (by simpa using hk9), PEqualNP.Outside.L_meta_3166.ofFn_getD, dif_pos hk9]
    have hnk : N1.getD k false = x ⟨k, hk9⟩ := by
      rw [hN1, PEqualNP.Outside.L_meta_3166.fold_getD _ _ k (by simpa using hk9),
        PEqualNP.Outside.L_meta_3166.ofFn_getD, dif_pos hk9]
    have hvg : g.op.eval (g.inputs.map fun i => W1.getD i false) = N1.getD k false := by
      rw [hop, hnk]
      rcases hins with e | e
      · rw [e]
        change (W1.getD 9 false || (W1.getD k false || false)) = _
        rw [hw9, hwk]
        rcases hk with h0 | h2
        · subst h0; exact PEqualNP.Outside.L_meta_3166.ab1 _ _
        · subst h2; exact PEqualNP.Outside.L_meta_3166.ab2 _ _
      · rw [e]
        change (W1.getD k false || (W1.getD 9 false || false)) = _
        rw [hw9, hwk]
        rcases hk with h0 | h2
        · subst h0; exact PEqualNP.Outside.L_meta_3166.ab3 _ _
        · subst h2; exact PEqualNP.Outside.L_meta_3166.ab4 _ _
    -- phase 2: the gates after g
    have hW2l : (PEqualNP.Outside.L_meta_3166.step W1 g).length = 11 + A.length := by
      simp [PEqualNP.Outside.L_meta_3166.step, hW1l]; omega
    have ph3 := PEqualNP.Outside.L_meta_3166.phase ρ 2 9 B (PEqualNP.Outside.L_meta_3166.step W1 g) N1
      (by rw [hW2l, hN1l]; omega)
      (by
        intro i h1 h2
        rw [hW2l] at h1 h2
        simp only [ρ]
        rw [if_neg (by omega), if_neg (by omega)])
      (by
        intro i h1 h2
        rw [hW2l] at h1
        by_cases hi : i < W1.length
        · obtain ⟨q1, q2⟩ := ph1.2 i hi h2
          refine ⟨q1, ?_⟩
          unfold PEqualNP.Outside.L_meta_3166.step
          rw [List.getD_append _ _ _ _ hi]
          exact q2
        · have hiE : i = W1.length := by omega
          have hρ : ρ i = k := by
            simp only [ρ]
            rw [if_neg (by omega), if_pos (by omega)]
          rw [hρ]
          refine ⟨by omega, ?_⟩
          rw [hiE]
          unfold PEqualNP.Outside.L_meta_3166.step
          rw [PEqualNP.Outside.L_meta_3166.snoc_getD_len _ _ _ rfl]
          exact hvg)
      (by
        intro j hj a ha
        rw [hW2l]
        have h1 := hrb (A.length + 1 + j) (by rw [hG]; simp; omega) a (by
          unfold PEqualNP.MetaComplexity.NestedCover.gateAt
          rw [hG, PEqualNP.Outside.L_meta_3166.getD_right A g B _ j hj]; exact ha)
        refine ⟨by omega, ?_⟩
        intro e
        exact hB' _ (List.getElem_mem hj) (e ▸ ha))
    -- read off the outputs
    have hold : C.eval inp = (B.foldl PEqualNP.Outside.L_meta_3166.step
        (PEqualNP.Outside.L_meta_3166.step W1 g)).getD C.output false := by
      show (C.gates.foldl PEqualNP.Outside.L_meta_3166.step inp).getD C.output false = _
      rw [hG, List.foldl_append, List.foldl_cons]
    have hnew : (PEqualNP.CircuitLowerBounds.Circuit.mk
        (A.map (PEqualNP.Outside.L_meta_3166.mapGate ρ) ++ B.map (PEqualNP.Outside.L_meta_3166.mapGate ρ))
        (ρ C.output)).eval (List.ofFn x) =
        ((B.map (PEqualNP.Outside.L_meta_3166.mapGate ρ)).foldl PEqualNP.Outside.L_meta_3166.step N1).getD
          (ρ C.output) false := by
      show ((A.map _ ++ B.map _).foldl PEqualNP.Outside.L_meta_3166.step (List.ofFn x)).getD _ false = _
      rw [List.foldl_append]
    rw [hnew]
    show _ = C.eval inp
    rw [hold]
    have hWf : (B.foldl PEqualNP.Outside.L_meta_3166.step (PEqualNP.Outside.L_meta_3166.step W1 g)).length
        = 11 + A.length + B.length := by
      rw [PEqualNP.Outside.L_meta_3166.fold_len, hW2l]
    by_cases ho : C.output < 11 + A.length + B.length
    · exact ((ph3.2 C.output (by rw [hWf]; exact ho) hout).2).symm
    · have hNf := ph3.1
      rw [hWf] at hNf
      have hρ : ρ C.output = C.output - 2 := by
        simp only [ρ]
        rw [if_neg (by omega), if_neg (by omega)]
      have e1 : (B.foldl PEqualNP.Outside.L_meta_3166.step (PEqualNP.Outside.L_meta_3166.step W1 g)).getD
          C.output false = false := List.getD_eq_default _ _ (by rw [hWf]; omega)
      have e2 : ((B.map (PEqualNP.Outside.L_meta_3166.mapGate ρ)).foldl PEqualNP.Outside.L_meta_3166.step N1).getD
          (ρ C.output) false = false := List.getD_eq_default _ _ (by rw [hρ]; omega)
      rw [e1, e2]
