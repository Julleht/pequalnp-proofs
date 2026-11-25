import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- Reduction of L-meta-1772. Open core (hSound): some least monotone circuit for the edge
-- function has every AND gate sound (true only on inputs that contain an edge). Normal form
-- (hClean, no graph condition): a sound monotone circuit for the edge function can be rewritten,
-- without growing, so that every AND gate reads only earlier wires that are true at some
-- one-vertex input, and every OR gate true at some one-vertex input reads only such earlier wires
-- (the method of PR 11479, fix_all). PROVED HERE: from that normal form every AND gate owns an
-- edge, and the circuit is still least. An AND gate reading wires a, b true at 1_za, 1_zb is true
-- at 1_{za zb} (monotonicity), so za zb is an edge (soundness); every AND gate strictly below it is
-- reached through wires true at a one-vertex input, so it would be true at a one-vertex input,
-- which soundness forbids: the gate owns za zb.
theorem PEqualNP.Outside.R_meta_1772_29
    (hSound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∀ x : Fin n → Bool, gateVal n C j x = true →
            ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (hClean : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      Monotone2 C → circuitFun n C = graphFun G ∅ →
      (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∀ x : Fin n → Bool, gateVal n C j x = true →
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
        let T := fun i : ℕ => ∃ z : Fin n, (D.wires (List.ofFn (pairInput z z))).getD i false = true
        ∀ j < D.gates.length, ((gateAt D j).op = GateOp.and → ∀ x : Fin n → Bool,
          gateVal n D j x = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∧
          ∀ i ∈ (gateAt D j).inputs, ((gateAt D j).op = GateOp.and → i < n + j ∧ T i) ∧
            ((gateAt D j).op = GateOp.or → T (n + j) → i < n + j → T i)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11 := by
  intro n G _ tri four
  obtain ⟨C0, hmin0, hfun0, hs0⟩ := hSound n G tri four
  obtain ⟨C, hmono, hsize, hfun, hN⟩ := hClean n G C0 hmin0.1 hfun0 hs0
  have hs : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ x : Fin n → Bool,
      gateVal n C j x = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true :=
    fun j hj => (hN j hj).1
  have hA : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ i ∈ (gateAt C j).inputs,
      i < n + j ∧ ∃ z : Fin n, (C.wires (List.ofFn (pairInput z z))).getD i false = true :=
    fun j hj hop i hi => ((hN j hj).2 i hi).1 hop
  have hO : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      (∃ z : Fin n, gateVal n C j (pairInput z z) = true) →
      ∀ i ∈ (gateAt C j).inputs, i < n + j →
        ∃ z : Fin n, (C.wires (List.ofFn (pairInput z z))).getD i false = true :=
    fun j hj hop hT i hi => ((hN j hj).2 i hi).2 hop hT
  refine ⟨C, ⟨hmono, fun D hD hDf =>
    hsize.trans (hmin0.2 D hD (hDf.trans (hfun.trans hfun0.symm)))⟩, hfun, ?_⟩
  -- generic facts on lists built by appending one entry per gate
  have gfold : ∀ (α : Type) (F : List α → Gate → α) (L : List Gate) (acc : List α),
      (L.foldl (fun a g => a ++ [F a g]) acc).length = acc.length + L.length ∧
      ∀ i < acc.length, ∀ d : α,
        (L.foldl (fun a g => a ++ [F a g]) acc).getD i d = acc.getD i d := by
    intro α F L
    induction L with
    | nil => intro acc; exact ⟨by simp, fun i _ d => rfl⟩
    | cons g L ih =>
      intro acc
      obtain ⟨h1, h2⟩ := ih (acc ++ [F acc g])
      refine ⟨?_, ?_⟩
      · rw [List.foldl_cons, h1]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · intro i hi d
        rw [List.foldl_cons, h2 i (by simp only [List.length_append]; omega) d]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have gpos : ∀ (α : Type) (F : List α → Gate → α) (L : List Gate) (acc : List α) (k : ℕ)
      (hk : k < L.length) (d : α),
      ((L.take k).foldl (fun a g => a ++ [F a g]) acc).length = acc.length + k ∧
      (L.foldl (fun a g => a ++ [F a g]) acc).getD (acc.length + k) d =
        F ((L.take k).foldl (fun a g => a ++ [F a g]) acc) L[k] ∧
      ∀ i < acc.length + k, (L.foldl (fun a g => a ++ [F a g]) acc).getD i d =
        ((L.take k).foldl (fun a g => a ++ [F a g]) acc).getD i d := by
    intro α F L acc k hk d
    have hPl : ((L.take k).foldl (fun a g => a ++ [F a g]) acc).length = acc.length + k := by
      rw [(gfold α F (L.take k) acc).1, List.length_take]
      omega
    have hL : L.foldl (fun a g => a ++ [F a g]) acc =
        (L.drop (k + 1)).foldl (fun a g => a ++ [F a g])
          ((L.take k).foldl (fun a g => a ++ [F a g]) acc ++
            [F ((L.take k).foldl (fun a g => a ++ [F a g]) acc) L[k]]) := by
      conv_lhs => rw [← List.take_append_drop k L]
      rw [List.foldl_append, List.drop_eq_getElem_cons hk, List.foldl_cons]
    have hG := (gfold α F (L.drop (k + 1))
      ((L.take k).foldl (fun a g => a ++ [F a g]) acc ++
        [F ((L.take k).foldl (fun a g => a ++ [F a g]) acc) L[k]])).2
    have hPl1 : ((L.take k).foldl (fun a g => a ++ [F a g]) acc ++
        [F ((L.take k).foldl (fun a g => a ++ [F a g]) acc) L[k]]).length = acc.length + k + 1 := by
      rw [List.length_append, hPl]; rfl
    refine ⟨hPl, ?_, ?_⟩
    · rw [hL, hG (acc.length + k) (by omega) d]
      rw [← hPl]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
        Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    · intro i hi
      rw [hL, hG i (by omega) d]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (hPl ▸ hi)]
  -- the circuit's wires and cones in that shape
  let Fw : List Bool → Gate → Bool := fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)
  have hwires : ∀ y : List Bool, C.wires y = C.gates.foldl (fun a g => a ++ [Fw a g]) y :=
    fun _ => rfl
  let Fc : List (List ℕ) → Gate → List ℕ := fun cs g =>
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])
  have hcones : cones n C = C.gates.foldl (fun a g => a ++ [Fc a g]) [] := rfl
  have hgat : ∀ j (hj : j < C.gates.length), gateAt C j = C.gates[j] := by
    intro j hj
    show C.gates.getD j ⟨GateOp.or, []⟩ = _
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have hgv : ∀ (j : ℕ) (x : Fin n → Bool),
      gateVal n C j x = (C.wires (List.ofFn x)).getD (n + j) false := fun _ _ => rfl
  have hpi : ∀ a b w : Fin n, pairInput a b w = decide (w = a ∨ w = b) := fun _ _ _ => rfl
  have hand : ∀ l : List Bool, GateOp.eval GateOp.and l = l.all id := fun _ => rfl
  have hor : ∀ l : List Bool, GateOp.eval GateOp.or l = l.any id := fun _ => rfl
  have hlegal : ∀ j < C.gates.length, ((gateAt C j).op = GateOp.and ∨
      (gateAt C j).op = GateOp.or) ∧ (gateAt C j).inputs.length ≤ 2 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hmono (gateAt C j) (by rw [hgat j hj]; exact List.getElem_mem hj)
    refine ⟨?_, h2⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h1
  -- an AND gate whose inputs are earlier wires, all true, is true
  have andval : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ x : Fin n → Bool,
      (∀ i ∈ (gateAt C j).inputs, i < n + j ∧ (C.wires (List.ofFn x)).getD i false = true) →
      gateVal n C j x = true := by
    intro j hj hop x hin
    obtain ⟨_, h2, h3⟩ := gpos Bool Fw C.gates (List.ofFn x) j hj false
    rw [List.length_ofFn] at h2 h3
    rw [hgv, hwires, h2]
    rw [hgat j hj] at hop hin
    show GateOp.eval _ _ = true
    rw [hop, hand, List.all_eq_true]
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    obtain ⟨hlt, hv⟩ := hin i hi
    rw [hwires, h3 i hlt] at hv
    exact hv
  -- monotonicity of the wires
  have hget : ∀ (a : List Bool) (v : Bool) (i : ℕ), (a ++ [v]).getD i false = true →
      (i < a.length ∧ a.getD i false = true) ∨ (i = a.length ∧ v = true) := by
    intro a v i h
    by_cases h1 : i < a.length
    · left
      refine ⟨h1, ?_⟩
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left h1] using h
    · right
      by_cases h2 : i = a.length
      · subst h2
        refine ⟨rfl, ?_⟩
        simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] using h
      · exfalso
        have h3 : a.length + 1 ≤ i := by omega
        have h4 : (a ++ [v]).getD i false = false := by
          have h5 : (a ++ [v]).length ≤ i := by
            rw [List.length_append]
            exact h3
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h5]
          rfl
        rw [h4] at h
        exact Bool.false_ne_true h
  have hput : ∀ (a : List Bool) (v : Bool) (i : ℕ), i < a.length → a.getD i false = true →
      (a ++ [v]).getD i false = true := by
    intro a v i hi h
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi] using h
  have hputl : ∀ (a : List Bool) (v : Bool), v = true → (a ++ [v]).getD a.length false = true := by
    intro a v h
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] using h
  have mono : ∀ L : List Gate, (∀ g ∈ L, (g.op = GateOp.and ∨ g.op = GateOp.or)) →
      ∀ a b : List Bool, a.length = b.length →
      (∀ i, a.getD i false = true → b.getD i false = true) →
      ∀ i, (L.foldl (fun a g => a ++ [Fw a g]) a).getD i false = true →
        (L.foldl (fun a g => a ++ [Fw a g]) b).getD i false = true := by
    intro L
    induction L with
    | nil => intro _ a b _ hab; exact hab
    | cons g L ih =>
      intro hL a b hlen hab
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g' hg' => hL g' (List.mem_cons_of_mem g hg'))
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
      · intro i hi
        rcases hget a (Fw a g) i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hput b _ i (hlen ▸ h1) (hab i h2)
        · subst h1
          rw [hlen]
          apply hputl
          have hrd : ∀ j ∈ g.inputs, a.getD j false = true → b.getD j false = true :=
            fun j _ => hab j
          rcases hL g List.mem_cons_self with ho | ho
          · show GateOp.eval _ _ = true
            have h2' : GateOp.eval g.op (g.inputs.map fun i => a.getD i false) = true := h2
            rw [ho, hand, List.all_eq_true] at h2' ⊢
            intro c hc
            obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
            exact hrd j hj (h2' _ (List.mem_map.2 ⟨j, hj, rfl⟩))
          · show GateOp.eval _ _ = true
            have h2' : GateOp.eval g.op (g.inputs.map fun i => a.getD i false) = true := h2
            rw [ho, hor, List.any_eq_true] at h2' ⊢
            obtain ⟨c, hc, hcv⟩ := h2'
            obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
            exact ⟨_, List.mem_map.2 ⟨j, hj, rfl⟩, hrd j hj hcv⟩
  have hallops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hmono g hg).1
  have hofn : ∀ (x y : Fin n → Bool), (∀ w, x w = true → y w = true) →
      ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
    intro x y hxy i h
    by_cases hi : i < n
    · have ex : ∀ z : Fin n → Bool, (List.ofFn z).getD i false = z ⟨i, hi⟩ := by
        intro z
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]
        rfl
      rw [ex] at h ⊢
      exact hxy _ h
    · have ex : (List.ofFn x).getD i false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [List.length_ofFn]; omega)]
        rfl
      rw [ex] at h
      exact absurd h Bool.false_ne_true
  have wmono : ∀ (x y : Fin n → Bool), (∀ w, x w = true → y w = true) →
      ∀ i, (C.wires (List.ofFn x)).getD i false = true →
        (C.wires (List.ofFn y)).getD i false = true := by
    intro x y hxy i h
    rw [hwires] at h ⊢
    exact mono C.gates hallops _ _ (by simp only [List.length_ofFn]) (hofn x y hxy) i h
  -- no AND gate is true at a one-vertex input
  have nosingle : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → ∀ z : Fin n,
      gateVal n C i (pairInput z z) = true → False := by
    intro i hi hop z hz
    obtain ⟨u, v, huv, hu, hv⟩ := hs i hi hop _ hz
    rw [hpi] at hu hv
    simp only [or_self, decide_eq_true_eq] at hu hv
    rw [hu, hv] at huv
    exact huv.ne rfl
  -- the cone of a gate is reached through the wires it reads
  have conestep : ∀ k < C.gates.length, ∀ i, InCone n C i k →
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ (i = w - n ∨ InCone n C i (w - n)) := by
    intro k hk i hi
    obtain ⟨h1, h2, h3⟩ := gpos (List ℕ) Fc C.gates [] k hk []
    have hi' : i ∈ (cones n C).getD k [] := hi
    rw [hcones] at hi'
    simp only [List.length_nil, Nat.zero_add] at h1 h2 h3
    rw [h2] at hi'
    obtain ⟨w, hw, hiw⟩ := List.mem_flatMap.1 hi'
    obtain ⟨hw1, hw2⟩ := List.mem_filter.1 hw
    rw [h1, decide_eq_true_eq] at hw2
    refine ⟨w, by rw [hgat k hk]; exact hw1, hw2.1, hw2.2, ?_⟩
    rcases List.mem_cons.1 hiw with e | e
    · exact Or.inl e
    · right
      show i ∈ (cones n C).getD (w - n) []
      rw [hcones, h3 (w - n) (by omega)]
      exact e
  -- wires true at a one-vertex input
  let T : ℕ → Prop := fun w => ∃ z : Fin n, (C.wires (List.ofFn (pairInput z z))).getD w false = true
  have pure : ∀ k, k < C.gates.length → T (n + k) → ∀ i, InCone n C i k → T (n + i) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hT i hi
      obtain ⟨w, hw, hnw, hwk, halt⟩ := conestep k hk i hi
      have hTw : T w := by
        rcases (hlegal k hk).1 with ha | ho
        · exact (hA k hk ha w hw).2
        · exact hO k hk ho hT w hw hwk
      have he : n + (w - n) = w := by omega
      rcases halt with e | e
      · rw [e, he]; exact hTw
      · exact ih (w - n) (by omega) (by omega) (by rw [he]; exact hTw) i e
  -- every AND gate owns an edge
  intro j hj hop
  have hgood : ∀ i ∈ (gateAt C j).inputs, i < n + j ∧ T i := hA j hj hop
  have hbelow : ∀ i, InCone n C i j → T (n + i) := by
    intro i hi
    obtain ⟨w, hw, hnw, hwj, halt⟩ := conestep j hj i hi
    have hTw : T w := (hgood w hw).2
    have he : n + (w - n) = w := by omega
    rcases halt with e | e
    · rw [e, he]; exact hTw
    · exact pure (w - n) (by omega) (by rw [he]; exact hTw) i e
  have hlen := (hlegal j hj).2
  rcases hl : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exfalso
    have hv : gateVal n C j (fun _ => false) = true :=
      andval j hj hop _ (by rw [hl]; intro i hi; exact absurd hi List.not_mem_nil)
    obtain ⟨u, v, _, hu, _⟩ := hs j hj hop _ hv
    exact Bool.false_ne_true hu
  · exfalso
    obtain ⟨hlt, z, hz⟩ := hgood a (by rw [hl]; exact List.mem_singleton_self a)
    apply nosingle j hj hop z
    apply andval j hj hop
    rw [hl]
    intro i hi
    rw [List.mem_singleton.1 hi]
    exact ⟨hlt, hz⟩
  · obtain ⟨hla, za, hza⟩ := hgood a (by rw [hl]; exact List.mem_cons_self)
    obtain ⟨hlb, zb, hzb⟩ := hgood b (by rw [hl]; exact List.mem_cons_of_mem a List.mem_cons_self)
    have hxa : ∀ w, pairInput za za w = true → pairInput za zb w = true := by
      intro w hw
      rw [hpi] at hw ⊢
      simp only [or_self, decide_eq_true_eq] at hw
      simp only [hw, true_or, decide_true]
    have hxb : ∀ w, pairInput zb zb w = true → pairInput za zb w = true := by
      intro w hw
      rw [hpi] at hw ⊢
      simp only [or_self, decide_eq_true_eq] at hw
      simp only [hw, or_true, decide_true]
    have hval : gateVal n C j (pairInput za zb) = true := by
      apply andval j hj hop
      rw [hl]
      intro i hi
      rcases List.mem_cons.1 hi with e | e
      · rw [e]; exact ⟨hla, wmono _ _ hxa a hza⟩
      · rw [List.mem_singleton.1 e]; exact ⟨hlb, wmono _ _ hxb b hzb⟩
    obtain ⟨u, v, huv, hu, hv⟩ := hs j hj hop _ hval
    rw [hpi] at hu hv
    simp only [decide_eq_true_eq] at hu hv
    have hadj : G.Adj za zb := by
      rcases hu with e1 | e1 <;> rcases hv with e2 | e2 <;> rw [e1, e2] at huv
      · exact absurd rfl huv.ne
      · exact huv
      · exact huv.symm
      · exact absurd rfl huv.ne
    refine ⟨za, zb, hadj, hj, hop, hval, ?_⟩
    intro i hij hc hiand
    exfalso
    obtain ⟨z, hz⟩ := hbelow i hc
    exact nosingle i (by omega) hiand z hz
  · exfalso
    rw [hl] at hlen
    simp only [List.length_cons] at hlen
    omega
