import PEqualNP.Defs

-- Reduction of L-meta-2850: cut by the gates that read input 0.
-- h1 is merged L_meta_2331. If every reader of wire 0 is a NOT gate (or there is none), replacing a
-- NOT gate whose first input is wire 0 by AND of wire 0 gives a circuit of the same size computing the
-- edge function, against h1. One AND reader: h2. One OR reader: h3.
theorem PEqualNP.Outside.R_meta_2850_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates = [g] ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then !x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (h3 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates = [g] ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then !x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → x2 = Bool.true → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  have key : ∀ y : Bool, (true != y) = !y := by decide
  have eNot : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.not.eval l = !(l.headD false) :=
    fun _ => rfl
  have eAnd : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun _ => rfl
  have eFun : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin n → Bool),
      PEqualNP.MetaComplexity.circuitFun n C x =
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD C.output false := fun _ _ _ => rfl
  have app_getD : ∀ (w v : List Bool) (z : Bool), w.length = v.length →
      (∀ k, k ≠ 0 → w.getD k false = v.getD k false) →
      ∀ k, k ≠ 0 → (w ++ [z]).getD k false = (v ++ [z]).getD k false := by
    intro w v z hlen heq k hk
    by_cases hlt : k < w.length
    · have hlt2 : k < v.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hlt, List.getElem?_append_left hlt2]
      have := heq k hk
      rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this
    · have hle1 : w.length ≤ k := by omega
      have hle2 : v.length ≤ k := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right hle1, List.getElem?_append_right hle2, hlen]
  have app_getD0 : ∀ (w : List Bool) (z : Bool), 0 < w.length →
      (w ++ [z]).getD 0 false = w.getD 0 false := by
    intro w z hw
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
  have fold_getD0 : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), 0 < w.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD 0 false =
        w.getD 0 false := by
    intro gs
    induction gs with
    | nil => intro w _; rfl
    | cons g gs ih =>
      intro w hw
      rw [List.foldl_cons, ih _ (by simp), app_getD0 _ _ hw]
  intro C b hfan hsize hlen hb
  subst hb
  simp only [key]
  by_cases hA : ∃ g ∈ C.gates, g.inputs.contains 0 = true ∧ g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, hg, h0, hop⟩ := hA
    have hm : g ∈ List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains 0) C.gates :=
      List.mem_filter.mpr ⟨hg, h0⟩
    have hfl : List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains 0) C.gates = [g] := by
      generalize List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains 0) C.gates = l at hm hlen ⊢
      rcases l with _ | ⟨a, _ | ⟨c, l⟩⟩
      · simp at hm
      · simp at hm
        rw [hm]
      · simp at hlen
    have hset := (hfan g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hset
    rcases hset with hop' | hop' | hop'
    · exact h2 C hfan hsize ⟨g, hfl, hop'⟩
    · exact h3 C hfan hsize ⟨g, hfl, hop'⟩
    · exact absurd hop' hop
  · have hnot : ∀ g ∈ C.gates, g.inputs.contains 0 = true → g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro g hg h0
      exact Classical.byContradiction fun hc => hA ⟨g, hg, h0, hc⟩
    by_cases hout : C.output = 0
    · refine ⟨fun _ => false, ?_⟩
      simp only [eFun, hout]
      rw [fold_getD0 _ _ (by simp)]
      decide
    · let f : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g =>
        if g.inputs.head? = some 0 then ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0]⟩ else g
      have gate_eq : ∀ g : PEqualNP.CircuitLowerBounds.Gate,
          (g.inputs.contains 0 = true → g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
          ∀ (w v : List Bool), w.getD 0 false = !(v.getD 0 false) →
          (∀ k, k ≠ 0 → w.getD k false = v.getD k false) →
          g.op.eval (g.inputs.map fun i => w.getD i false) =
            (f g).op.eval ((f g).inputs.map fun i => v.getD i false) := by
        intro g hg w v h0 heq
        by_cases hh : g.inputs.head? = some 0
        · have hfg : f g = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0]⟩ := if_pos hh
          rw [hfg]
          cases hi : g.inputs with
          | nil => rw [hi] at hh; simp at hh
          | cons a rest =>
            rw [hi] at hh
            simp at hh
            subst hh
            have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.not := hg (by simp [hi])
            rw [hop]
            simpa [eNot, eAnd, hi] using h0
        · have hfg : f g = g := if_neg hh
          rw [hfg]
          by_cases hc : g.inputs.contains 0 = true
          · have hop := hg hc
            rw [hop]
            cases hi : g.inputs with
            | nil => rw [hi] at hc; simp at hc
            | cons a rest =>
              have ha : a ≠ 0 := by
                intro ha0
                apply hh
                rw [hi, ha0]
                rfl
              simpa [eNot, hi] using heq a ha
          · congr 1
            apply List.map_congr_left
            intro i hi
            apply heq
            intro hi0
            subst hi0
            apply hc
            simpa using hi
      have fold_eq : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
          (∀ g ∈ gs, g.inputs.contains 0 = true → g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
          ∀ (w v : List Bool), w.length = v.length → 0 < w.length →
          w.getD 0 false = !(v.getD 0 false) →
          (∀ k, k ≠ 0 → w.getD k false = v.getD k false) →
          ∀ k, k ≠ 0 →
            (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD k false =
            ((gs.map f).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v).getD k false := by
        intro gs
        induction gs with
        | nil => intro _ w v _ _ _ heq; exact heq
        | cons g gs ih =>
          intro hgs w v hlen hpos h0 heq
          rw [List.map_cons, List.foldl_cons, List.foldl_cons,
            gate_eq g (hgs g (by simp)) w v h0 heq]
          apply ih (fun g' hg' => hgs g' (by simp [hg']))
          · simp [hlen]
          · simp
          · rw [app_getD0 _ _ hpos, app_getD0 _ _ (by omega)]
            exact h0
          · exact app_getD _ _ _ hlen heq
      refine Classical.byContradiction fun hall => ?_
      have hall' : ∀ x : Fin 9 → Bool,
          PEqualNP.MetaComplexity.circuitFun 9 C (fun x8 => if x8 = 0 then !x 0 else x x8) =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
            x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) :=
        fun x => Classical.byContradiction fun hne => hall ⟨x, hne⟩
      let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map f, C.output⟩
      have hfan' : PEqualNP.MetaComplexity.FanInTwo C' := by
        intro g' hg'
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
        by_cases hh : g.inputs.head? = some 0
        · have hfg : f g = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0]⟩ := if_pos hh
          rw [hfg]
          simp
        · have hfg : f g = g := if_neg hh
          rw [hfg]
          exact hfan g hg
      have hsize' : C'.size = C.size := List.length_map _
      have hfun : PEqualNP.MetaComplexity.circuitFun 9 C' = fun (x3 : Fin 9 → Bool) =>
          x3 0 && x3 1 || x3 1 && x3 2 || x3 2 && x3 3 || x3 3 && x3 4 || x3 4 && x3 0 || x3 0 && x3 5 ||
            x3 1 && x3 6 || x3 2 && x3 7 || x3 3 && x3 8 || x3 5 && x3 7 || x3 6 && x3 8 || x3 8 && x3 5 := by
        funext x
        rw [← hall' x]
        simp only [eFun]
        symm
        apply fold_eq C.gates hnot
        · simp
        · simp
        · simp
        · intro k hk
          by_cases hlt : k < 9
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_ofFn, List.getElem?_ofFn]
            have hne : (⟨k, hlt⟩ : Fin 9) ≠ 0 := by
              intro h0
              exact hk (congrArg Fin.val h0)
            simp [hlt, hne]
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
        · exact hout
      have h15 := h1 C' hfan' hfun
      rw [hsize'] at h15
      exact absurd hsize (by omega)
