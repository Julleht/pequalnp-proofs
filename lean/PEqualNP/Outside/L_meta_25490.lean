import PEqualNP.Defs

-- L-meta-25490: on two distinct missing columns the spare is on with all rows off, so it is no input: a gate j.
-- If j were row w's OR, or an AND reading it, that OR is on at col c' (Gw c' on, Gv c' off), so on at oneEach v c';
-- then oneEach v c' and rows v,w at c' agree off w (strong induction), against eval >= eval (oneEach w c') = true.
-- If j is an OR reading row w's OR, symmetric with v's OR on at oneEach w c. Wire machinery copied from L_meta_25488.

namespace PEqualNP.Outside.L_meta_25490_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- copied from PEqualNP.Outside.L_meta_25488_aux (lean/PEqualNP/Outside/L_meta_25488.lean),
-- copied via L_meta_25479_aux from PEqualNP.Outside.L_meta_23962_aux (lean/PEqualNP/Outside/L_meta_23962.lean)
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

theorem wires_low (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  change (C.gates.foldl (fun w g => w ++ [readGate w g]) x).getD i false = _
  exact getD_of_initial (foldl_snoc_keeps readGate C.gates x) hi false

theorem mono_wires (N : ℕ) (C : Circuit) (hmono : Monotone2 C) (hback : ReadsBack N C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ w, (C.wires x).getD w false = true → (C.wires y).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlo : w < N
    · rw [wires_low C y w (by omega)]
      rw [wires_low C x w (by omega)] at hw
      exact hxy w hw
    by_cases hhi : N + C.gates.length ≤ w
    · rw [wire_past C x w (by omega)] at hw
      exact absurd hw (by simp)
    obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
    have hj : j < C.gates.length := by omega
    rw [gate_value N C x hx hback j hj] at hw
    rw [gate_value N C y hy hback j hj]
    have hmem : gateAt C j ∈ C.gates := by
      rw [show gateAt C j = C.gates[j] from List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hop := (hmono _ hmem).1
    have hin : ∀ i ∈ (gateAt C j).inputs,
        (C.wires x).getD i false = true → (C.wires y).getD i false = true :=
      fun i hi => ih i (by have := hback j hj i hi; omega)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h <;> rw [h] at hw ⊢ <;> simp only [GateOp.eval] at hw ⊢
    · simp only [List.all_eq_true, List.mem_map] at hw ⊢
      rintro _ ⟨i, hi, rfl⟩
      exact hin i hi (hw _ ⟨i, hi, rfl⟩)
    · simp only [List.any_eq_true, List.mem_map] at hw ⊢
      obtain ⟨_, ⟨i, hi, rfl⟩, hv⟩ := hw
      exact ⟨_, ⟨i, hi, rfl⟩, hin i hi hv⟩

theorem agree_off (N : ℕ) (C : Circuit) (hback : ReadsBack N C) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (B : List ℕ)
    (hin : ∀ i < N, i ∉ B → x.getD i false = y.getD i false)
    (hgate : ∀ j < C.gates.length, N + j ∉ B → (∃ b ∈ B, b ∈ (gateAt C j).inputs) →
      (C.wires x).getD (N + j) false = (C.wires y).getD (N + j) false) :
    ∀ w, w ∉ B → (C.wires x).getD w false = (C.wires y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlo : w < N
    · rw [wires_low C x w (by omega), wires_low C y w (by omega)]
      exact hin w hlo hw
    by_cases hhi : N + C.gates.length ≤ w
    · rw [wire_past C x w (by omega), wire_past C y w (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
    have hj : j < C.gates.length := by omega
    by_cases hr : ∃ b ∈ B, b ∈ (gateAt C j).inputs
    · exact hgate j hj hw hr
    rw [gate_value N C x hx hback j hj, gate_value N C y hy hback j hj]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact ih i (hback j hj i hi) (fun hiB => hr ⟨i, hiB, hi⟩)

theorem or_value (N : ℕ) (C : Circuit) (z : List Bool) (hz : z.length = N)
    (hback : ReadsBack N C) (k : ℕ) (hk : k < C.gates.length) (a b : ℕ)
    (hop : (gateAt C k).op = GateOp.or)
    (hin : (gateAt C k).inputs = [a, b] ∨ (gateAt C k).inputs = [b, a]) :
    (C.wires z).getD (N + k) false = ((C.wires z).getD a false || (C.wires z).getD b false) := by
  rw [gate_value N C z hz hback k hk, hop]
  rcases hin with h | h
  · simp [h, GateOp.eval]
  · simp [h, GateOp.eval, Bool.or_comm]


theorem col_length (n m : ℕ) (c : Fin m) :
    (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))).length = n + m := by
  simp

theorem col_getD (n m : ℕ) (c : Fin m) (i : ℕ) :
    (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))).getD i false =
      decide (i = n + c.val) := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    simp [List.getElem?_replicate, h]
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp [h2, Fin.ext_iff]
      omega
    · simp [h2]
      omega

end PEqualNP.Outside.L_meta_25490_aux

open PEqualNP.Outside.L_meta_25490_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25490 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (r : Fin n → Fin C.gates.length) (s : Fin n → ℕ) (v : Fin n),
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let wire := fun idx : Fin C.gates.length => n + m + idx.val
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length)
  let col := fun label : Fin m =>
    List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = label))
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  (∀ u : Fin n, C.output ≠ u.val) →
  (∀ c, ∃ u, G u c = false) →
  (∀ u w, u ≠ w → ∃ c, G u c = true ∧ G w c = false) →
  (∀ u : Fin n, reads u.val = 1 ∧ (gate (r u).val).op = .or ∧
    ((gate (r u).val).inputs = [u.val, s u] ∨
      (gate (r u).val).inputs = [s u, u.val])) →
  2 ≤ (Finset.univ.filter (fun c => G v c = false)).card →
  (∀ c, G v c = false → (C.wires (col c)).getD (s v) false = true) →
  ∃ j : Fin C.gates.length, s v = wire j ∧
    ∀ w, j ≠ r w ∧ wire (r w) ∉ (gate j.val).inputs := by
  classical
  intro n m G C r s v gate wire reads col hmono hback hrep hout hcol hinc hrow htwo hspare
  let N := n + m
  have hrow' : ∀ u : Fin n, readsIn C (Finset.range C.size) u.val = 1 ∧
      (gateAt C (r u).val).op = GateOp.or ∧
      ((gateAt C (r u).val).inputs = [u.val, s u] ∨ (gateAt C (r u).val).inputs = [s u, u.val]) :=
    hrow
  have hlen_col : ∀ c : Fin m, (col c).length = N := fun c => col_length n m c
  have hcolget : ∀ (c : Fin m) (i : ℕ), (col c).getD i false = decide (i = n + c.val) :=
    fun c i => col_getD n m c i
  have readerOf : ∀ u : Fin n, ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs → k = (r u).val := by
    intro u k hk hk'
    have hmi : u.val ∈ (gateAt C (r u).val).inputs := by
      rcases (hrow' u).2.2 with h | h <;> simp [h]
    exact only_reader C u.val k (r u).val hk (r u).isLt (hrow' u).1 hk' hmi
  have orR : ∀ u : Fin n, ∀ z : List Bool, z.length = N → (C.wires z).getD (N + (r u).val) false =
      ((C.wires z).getD u.val false || (C.wires z).getD (s u) false) :=
    fun u z hz => or_value N C z hz hback (r u).val (r u).isLt u.val (s u) (hrow' u).2.1 (hrow' u).2.2
  -- rows a, b differ; d meets a, misses b; if a's row OR is on at oneEach b d, the wires agree off a
  have key : ∀ a b : Fin n, a ≠ b → ∀ d : Fin m, G a d = true → G b d = false →
      (C.wires (oneEach b d)).getD (N + (r a).val) false = true → False := by
    intro a b hab d hGa hGb hra
    have hab' : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
    have ha := a.isLt
    have hb := b.isLt
    have hd := d.isLt
    let x3 := (List.range N).map (fun k => decide (k = a.val ∨ k = b.val ∨ k = n + d.val))
    have hl3 : x3.length = N := by simp [x3]
    have g3 : ∀ k, x3.getD k false = decide (k < N ∧ (k = a.val ∨ k = b.val ∨ k = n + d.val)) := by
      intro k
      simp only [x3, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range]
      by_cases hk : k < N <;> simp [hk]
    have e3 : C.eval x3 = true := by
      have e1 : C.eval (oneEach a d) = true := (hrep a d).trans hGa
      exact mono_wires N C hmono hback (oneEach a d) x3 (oneEach_length a d) hl3 (by
        intro k hk
        rw [oneEach_getD] at hk
        rw [g3]
        simp only [decide_eq_true_eq] at hk ⊢
        omega) C.output e1
    have e2 : C.eval (oneEach b d) = false := (hrep b d).trans hGb
    have a3 : (C.wires x3).getD a.val false = true := by
      rw [wires_low C x3 a.val (by omega), g3]; simp; omega
    have R3 : (C.wires x3).getD (N + (r a).val) false = true := by rw [orR a x3 hl3, a3]; simp
    have hag := agree_off N C hback (oneEach b d) x3 (oneEach_length b d) hl3 [a.val] (by
      intro k hk hka
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hka
      rw [oneEach_getD, g3]
      simp only [decide_eq_decide]
      constructor <;> intro h <;> omega) (by
      intro k hk _ hr
      obtain ⟨e, he, hek⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      have := readerOf a k hk hek
      subst this
      rw [hra, R3]) C.output (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact hout a)
    have : C.eval (oneEach b d) = C.eval x3 := hag
    rw [e2, e3] at this
    exact Bool.false_ne_true this
  -- the spare is on at two distinct singleton columns, so it is a gate wire
  obtain ⟨c1, hc1, c2, hc2, hc12⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter (fun c => G v c = false)).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc1 hc2
  have sp1 := hspare c1 hc1
  have sp2 := hspare c2 hc2
  have hge : N ≤ s v := by
    by_contra hlt
    push_neg at hlt
    rw [wires_low C (col c1) (s v) (by rw [hlen_col]; exact hlt), hcolget] at sp1
    rw [wires_low C (col c2) (s v) (by rw [hlen_col]; exact hlt), hcolget] at sp2
    simp only [decide_eq_true_eq] at sp1 sp2
    exact hc12 (Fin.ext (by omega))
  have hlt : s v < N + C.gates.length := by
    by_contra hh
    push_neg at hh
    rw [wire_past C (col c1) (s v) (by rw [hlen_col]; exact hh)] at sp1
    exact Bool.false_ne_true sp1
  let j : Fin C.gates.length := ⟨s v - N, by omega⟩
  have hsj : s v = N + j.val := by show s v = N + (s v - N); omega
  refine ⟨j, hsj, ?_⟩
  intro w
  have sv_in : s v ∈ (gateAt C (r v).val).inputs := by
    rcases (hrow' v).2.2 with h | h <;> simp [h]
  have hb_rv := hback (r v).val (r v).isLt (s v) sv_in
  by_cases hwv : w = v
  · rw [hwv]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have : j.val = (r v).val := by rw [h]
      omega
    · have h' : N + (r v).val ∈ (gateAt C j.val).inputs := h
      have := hback j.val j.isLt _ h'
      omega
  · obtain ⟨c', hGw', hGv'⟩ := hinc w v hwv
    obtain ⟨c, hGv, hGw⟩ := hinc v w (Ne.symm hwv)
    have hw := w.isLt
    have viaCol : (C.wires (col c')).getD (N + (r w).val) false = true → False := by
      intro hc
      apply key w v hwv c' hGw' hGv'
      exact mono_wires N C hmono hback (col c') (oneEach v c') (hlen_col c') (oneEach_length v c') (by
        intro k hk
        rw [hcolget] at hk
        rw [oneEach_getD]
        simp only [decide_eq_true_eq] at hk ⊢
        omega) _ hc
    have spc' := hspare c' hGv'
    refine ⟨fun h => ?_, fun h => ?_⟩
    · apply viaCol
      have : s v = N + (r w).val := by rw [hsj, h]
      rw [← this]
      exact spc'
    · have h' : N + (r w).val ∈ (gateAt C j.val).inputs := h
      have hmem : gateAt C j.val ∈ C.gates := by
        rw [show gateAt C j.val = C.gates[j.val] from List.getD_eq_getElem _ _ j.isLt]
        exact List.getElem_mem j.isLt
      have hop := (hmono _ hmem).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hand | hor
      · apply viaCol
        rw [hsj, gate_value N C (col c') (hlen_col c') hback j.val j.isLt, hand] at spc'
        simp only [GateOp.eval, List.all_eq_true, List.mem_map] at spc'
        exact spc' _ ⟨_, h', rfl⟩
      · apply key v w (Ne.symm hwv) c hGv hGw
        have rW : (C.wires (oneEach w c)).getD (N + (r w).val) false = true := by
          rw [orR w _ (oneEach_length w c), wire_input C w c w.val (by omega)]; simp
        have jW : (C.wires (oneEach w c)).getD (s v) false = true := by
          rw [hsj, gate_value N C (oneEach w c) (oneEach_length w c) hback j.val j.isLt, hor]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map]
          exact ⟨_, ⟨_, h', rfl⟩, rW⟩
        rw [orR v _ (oneEach_length w c), jW]
        simp
