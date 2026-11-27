import PEqualNP.Defs

-- L-meta-25479: compare the wires at oneEach u b' and oneEach u' b by strong induction on the wire.
-- Off the four inputs every wire agrees: a gate reading one of them is (only_reader) the pairing OR, true at both
-- inputs; every other gate reads earlier agreeing wires (ReadsBack). Wire lemmas copied from L_meta_23962.

namespace PEqualNP.Outside.L_meta_25479_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- copied from PEqualNP.Outside.L_meta_23962_aux (lean/PEqualNP/Outside/L_meta_23962.lean)
theorem foldl_snoc_keeps {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_initial {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_split {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).getD (init.length + j) d
      = F ((gs.take j).foldl (fun R g => R ++ [F R g]) init) gs[j] ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init) <+:
      gs.foldl (fun R g => R ++ [F R g]) init ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init).length = init.length + j := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [F R g]) init with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length F]; simp; omega
  have hpre : (P ++ [F P gs[j]]) <+: gs.foldl (fun R g => R ++ [F R g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_keeps F _ _
  refine ⟨?_, (List.prefix_append P _).trans hpre, hPl⟩
  rw [getD_of_initial hpre (by simp; omega), ← hPl]
  simp

def readGate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wireAt (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false = C.gates[j].op.eval
      (C.gates[j].inputs.map fun i => if i < x.length + j then (C.wires x).getD i false else false) := by
  obtain ⟨value,pre,len⟩ := foldl_snoc_split readGate C.gates x j hj false
  rw [show (C.wires x).getD (x.length + j) false = _ from value]
  unfold readGate
  congr 1
  apply List.map_congr_left
  intro i _
  split
  · exact (getD_of_initial pre (by omega) false).symm
  · apply List.getD_eq_default
    unfold readGate at len
    omega

theorem gate_value (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N)
    (hback : ReadsBack N C) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have hw := wireAt C x j hj
  have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [hx, ← he] at hw
  rw [hw]
  congr 1
  exact List.map_congr_left fun i hi => ite_eq_left (hback j hj i hi)

theorem only_reader (C : Circuit) (i j k : ℕ) (hj : j < C.size) (hk : k < C.size)
    (hc : readsIn C (Finset.range C.size) i = 1)
    (hij : i ∈ (gateAt C j).inputs) (hik : i ∈ (gateAt C k).inputs) : j = k := by
  by_contra h
  have hs : ({j, k} : Finset ℕ) ⊆ Finset.range C.size := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)
  have hsum : (∑ g ∈ ({j, k} : Finset ℕ), (gateAt C g).inputs.count i) ≤
      readsIn C (Finset.range C.size) i :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair h, hc] at hsum
  have ha := List.count_pos_iff.mpr hij
  have hb := List.count_pos_iff.mpr hik
  omega
-- end of the copy

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    simp only [List.getElem?_ofFn]
    simp [h, Fin.ext_iff]
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp [h2, Fin.ext_iff]
      have hu : ¬ i = u.val := by omega
      by_cases hv : i = n + v.val
      · simp [hv]
      · have hv' : ¬ i - n = v.val := by omega
        simp [hu, hv, hv']
    · simp [h2]
      omega

theorem wire_input (C : Circuit) {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n + m) :
    (C.wires (PEqualNP.Represents.oneEach u v)).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  change (C.gates.foldl (fun w g => w ++ [readGate w g]) (PEqualNP.Represents.oneEach u v)).getD i false = _
  rw [getD_of_initial (foldl_snoc_keeps readGate C.gates _) (by rw [oneEach_length]; exact hi),
    oneEach_getD]

theorem wire_past (C : Circuit) (x : List Bool) (i : ℕ) (hi : x.length + C.gates.length ≤ i) :
    (C.wires x).getD i false = false := by
  apply List.getD_eq_default
  change (C.gates.foldl (fun w g => w ++ [readGate w g]) x).length ≤ i
  rw [foldl_snoc_length]
  exact hi

end PEqualNP.Outside.L_meta_25479_aux

open PEqualNP.Outside.L_meta_25479_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25479 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
  (C : PEqualNP.CircuitLowerBounds.Circuit)
  (u u' : Fin n) (b b' : Fin m),
  let x := u.val
  let x' := u'.val
  let y := n + b.val
  let y' := n + b'.val
  let paired := fun (r c : ℕ) =>
    ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (g.inputs = [r, c] ∨ g.inputs = [c, r])
  u ≠ u' → b ≠ b' →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  paired x y → paired x' y' →
  (∀ w ∈ [x, x', y, y'],
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w = 1) →
  C.output ∉ [x, x', y, y'] →
  G u b' = G u' b := by
  classical
  intro n m G C u u' b b' x x' y y' paired huu hbb hback hrep h1 h2 hreads hout
  let N := n + m
  let x1 := oneEach u b'
  let x2 := oneEach u' b
  have hl1 : x1.length = N := oneEach_length u b'
  have hl2 : x2.length = N := oneEach_length u' b
  have hux : (u : ℕ) < n := u.isLt
  have hux' : (u' : ℕ) < n := u'.isLt
  have hbm : (b : ℕ) < m := b.isLt
  have hbm' : (b' : ℕ) < m := b'.isLt
  have huu' : (u : ℕ) ≠ u' := fun h => huu (Fin.ext h)
  have hbb' : (b : ℕ) ≠ b' := fun h => hbb (Fin.ext h)
  have rx : readsIn C (Finset.range C.size) x = 1 := hreads x (by simp)
  have rx' : readsIn C (Finset.range C.size) x' = 1 := hreads x' (by simp)
  have ry : readsIn C (Finset.range C.size) y = 1 := hreads y (by simp)
  have ry' : readsIn C (Finset.range C.size) y' = 1 := hreads y' (by simp)
  -- a gate reading one end of a pairing OR is that OR
  have key (r c : ℕ) (hp : paired r c) (hr : readsIn C (Finset.range C.size) r = 1)
      (hc : readsIn C (Finset.range C.size) c = 1) (z : List Bool) (hz : z.length = N)
      (j : ℕ) (hj : j < C.gates.length)
      (hrd : r ∈ (gateAt C j).inputs ∨ c ∈ (gateAt C j).inputs) :
      (C.wires z).getD (N + j) false = ((C.wires z).getD r false || (C.wires z).getD c false) := by
    obtain ⟨g, hg, hop, hin⟩ := hp
    obtain ⟨j1, hj1, hgj⟩ := List.mem_iff_getElem.mp hg
    have he : gateAt C j1 = g := (List.getD_eq_getElem _ _ hj1).trans hgj
    have hrm : r ∈ (gateAt C j1).inputs := by rw [he]; rcases hin with h | h <;> simp [h]
    have hcm : c ∈ (gateAt C j1).inputs := by rw [he]; rcases hin with h | h <;> simp [h]
    have hjj : j = j1 := by
      rcases hrd with h | h
      · exact only_reader C r j j1 hj hj1 hr h hrm
      · exact only_reader C c j j1 hj hj1 hc h hcm
    subst hjj
    rw [gate_value N C z hz hback j hj, he, hop]
    rcases hin with h | h
    · simp [h, GateOp.eval]
    · simp [h, GateOp.eval, Bool.or_comm]
  let V1 (i : ℕ) := (C.wires x1).getD i false
  let V2 (i : ℕ) := (C.wires x2).getD i false
  have v1x : V1 x = true := by
    change (C.wires x1).getD x false = true
    rw [wire_input C u b' x (by omega)]; simp [x]
  have v2y : V2 y = true := by
    change (C.wires x2).getD y false = true
    rw [wire_input C u' b y (by omega)]; simp [y]
  have v1y' : V1 y' = true := by
    change (C.wires x1).getD y' false = true
    rw [wire_input C u b' y' (by omega)]; simp [y']
  have v2x' : V2 x' = true := by
    change (C.wires x2).getD x' false = true
    rw [wire_input C u' b x' (by omega)]; simp [x']
  have agree : ∀ w, w ∉ [x, x', y, y'] → V1 w = V2 w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
      obtain ⟨hwx, hwx', hwy, hwy'⟩ := hw
      by_cases hlo : w < N
      · change (C.wires x1).getD w false = (C.wires x2).getD w false
        rw [wire_input C u b' w hlo, wire_input C u' b w hlo]
        simp only [x, x', y, y'] at hwx hwx' hwy hwy'
        simp [hwx, hwx', hwy, hwy']
      by_cases hhi : N + C.gates.length ≤ w
      · change (C.wires x1).getD w false = (C.wires x2).getD w false
        rw [wire_past C x1 w (by omega), wire_past C x2 w (by omega)]
      let j := w - N
      have hj : j < C.gates.length := by omega
      have hwj : w = N + j := by omega
      by_cases hA : x ∈ (gateAt C j).inputs ∨ y ∈ (gateAt C j).inputs
      · change (C.wires x1).getD w false = (C.wires x2).getD w false
        rw [hwj, key x y h1 rx ry x1 hl1 j hj hA, key x y h1 rx ry x2 hl2 j hj hA]
        change (V1 x || V1 y) = (V2 x || V2 y)
        rw [v1x, v2y]; simp
      by_cases hB : x' ∈ (gateAt C j).inputs ∨ y' ∈ (gateAt C j).inputs
      · change (C.wires x1).getD w false = (C.wires x2).getD w false
        rw [hwj, key x' y' h2 rx' ry' x1 hl1 j hj hB, key x' y' h2 rx' ry' x2 hl2 j hj hB]
        change (V1 x' || V1 y') = (V2 x' || V2 y')
        rw [v1y', v2x']; simp
      simp only [not_or] at hA hB
      change (C.wires x1).getD w false = (C.wires x2).getD w false
      rw [hwj, gate_value N C x1 hl1 hback j hj, gate_value N C x2 hl2 hback j hj]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hlt : i < w := hwj ▸ hback j hj i hi
      apply ih i hlt
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
      · exact hA.1 hi
      · exact hB.1 hi
      · exact hA.2 hi
      · exact hB.2 hi
  have ho := agree C.output hout
  have e1 : C.eval x1 = G u b' := hrep u b'
  have e2 : C.eval x2 = G u' b := hrep u' b
  rw [← e1, ← e2]
  exact ho
