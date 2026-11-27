import PEqualNP.Defs

-- L-meta-25551: the rest of the circuit sees a row of R only through the top wire, and on a column
-- outside B the top value is fixed by the row and the entry bit, monotonically in that bit. So
-- the rows of R carry at most three such patterns (two without an entry wire), and two rows with
-- one pattern differ only on columns of B. Columns are the same with the roles swapped.

namespace PEqualNP.Outside.L_meta_25551_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Represents

-- copied from scratchpad dectk/DecTK.lean (wiresFrom .. wires_eq, RB .. RB_single, gate_value;
-- itself from upstream/main L_meta_25021.lean)
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_init (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_init gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_init gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

/-- Gate `j` of `gs`, placed after `b` wires, reads only wires below `b + j`. -/
def RB (b : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < b + j

theorem readsBack_iff (n : ℕ) (C : Circuit) : ReadsBack n C ↔ RB n C.gates := Iff.rfl

theorem RB_nil (b : ℕ) : RB b [] := fun j hj => by simp at hj

theorem RB_append (b : ℕ) (gs1 gs2 : List Gate) :
    RB b (gs1 ++ gs2) ↔ RB b gs1 ∧ RB (b + gs1.length) gs2 := by
  constructor
  · intro h
    refine ⟨fun j hj i hi => ?_, fun j hj i hi => ?_⟩
    · exact h j (by simp; omega) i (by rwa [List.getD_append _ _ _ _ hj])
    · have := h (gs1.length + j) (by simp; omega) i
        (by rwa [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left])
      omega
  · rintro ⟨h1, h2⟩ j hj i hi
    by_cases hj1 : j < gs1.length
    · rw [List.getD_append _ _ _ _ hj1] at hi; exact h1 j hj1 i hi
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      have := h2 (j - gs1.length) (by simp at hj; omega) i hi; omega

theorem RB_single (b : ℕ) (g : Gate) : RB b [g] ↔ ∀ i ∈ g.inputs, i < b := by
  constructor
  · intro h i hi; simpa using h 0 (by simp) i (by simpa using hi)
  · intro h j hj i hi
    have : j = 0 := by simpa using hj
    subst this; simpa using h i (by simpa using hi)

/-- With earlier-wire reads, gate `j` of `gs` evaluated on the FINAL wire list gives wire
`x.length + j`. Strong induction over this proves values of hand-indexed tables. -/
theorem gate_value (x : List Bool) : ∀ gs : List Gate, RB x.length gs → ∀ j < gs.length,
    (wiresFrom gs x).getD (x.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval
        ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i => (wiresFrom gs x).getD i false) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ j hj; simp at hj
  | append_singleton gs g ih =>
    intro hR j hj
    have hR' := hR
    rw [RB_append, RB_single] at hR'
    obtain ⟨hR1, hR2⟩ := hR'
    simp only [List.length_append, List.length_singleton] at hj
    have hl : (wiresFrom gs x).length = x.length + gs.length := length_wiresFrom gs x
    have hsame : ∀ i, i < x.length + gs.length →
        (wiresFrom (gs ++ [g]) x).getD i false = (wiresFrom gs x).getD i false := by
      intro i hi
      rw [wiresFrom_snoc, getD_snoc, if_neg (by omega)]
    by_cases hj' : j < gs.length
    · rw [hsame _ (by omega), ih hR1 j hj', List.getD_append _ _ _ _ hj']
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [hsame i (by have := hR1 j hj' i hi; omega)]
    · have : j = gs.length := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero,
        wiresFrom_snoc, getD_snoc, if_pos hl.symm]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [← wiresFrom_snoc, hsame i (hR2 i hi)]

def val (C : Circuit) (x : List Bool) (w : ℕ) : Bool := (C.wires x).getD w false

theorem val_lt (C : Circuit) (x : List Bool) (w : ℕ) (h : w < x.length) :
    val C x w = x.getD w false := getD_wiresFrom _ _ _ h

theorem val_ge (C : Circuit) (x : List Bool) (w : ℕ) (h : x.length + C.size ≤ w) :
    val C x w = false := by
  unfold val
  rw [wires_eq, List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact h)]

theorem val_gate (C : Circuit) (x : List Bool) (N : ℕ) (hx : x.length = N) (hR : ReadsBack N C)
    (j : ℕ) (hj : j < C.size) :
    val C x (N + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (val C x)) := by
  subst hx; exact gate_value x C.gates hR j hj

/-- Wires agree on two inputs on a closed class: inputs of the class agree, and each gate wire
of the class either agrees or reads only wires of the class. -/
theorem closure (C : Circuit) (x y : List Bool) (N : ℕ) (hx : x.length = N) (hy : y.length = N)
    (hR : ReadsBack N C) (Good : ℕ → Prop)
    (hin : ∀ w < N, Good w → x.getD w false = y.getD w false)
    (hg : ∀ j < C.size, Good (N + j) →
      val C x (N + j) = val C y (N + j) ∨ ∀ i ∈ (gateAt C j).inputs, Good i) :
    ∀ w, Good w → val C x w = val C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < N
    · rw [val_lt C x w (by omega), val_lt C y w (by omega)]; exact hin w h1 hw
    by_cases h2 : N + C.size ≤ w
    · rw [val_ge C x w (by omega), val_ge C y w (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
    have hj : j < C.size := by omega
    rcases hg j hj hw with h | h
    · exact h
    · rw [val_gate C x N hx hR j hj, val_gate C y N hy hR j hj]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih i (by have := hR j hj i hi; omega) (h i hi)

theorem op_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (h : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
    intro hf i hi; exact h i hi (hf i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    rintro ⟨i, hi, hf⟩; exact ⟨i, hi, h i hi hf⟩

/-- An AND/OR region reading sources, its own wires and entry wires is monotone: equal sources
and entry values that can only rise make every region wire rise or stay. -/
theorem region_mono (C : Circuit) (x y : List Bool) (N : ℕ) (hx : x.length = N) (hy : y.length = N)
    (hR : ReadsBack N C) (region entry src : Finset ℕ) (hreg : region ⊆ Finset.range C.size)
    (hsrc : ∀ s ∈ src, s < N ∧ x.getD s false = y.getD s false)
    (hent : ∀ w ∈ entry, val C x w = true → val C y w = true)
    (hgates : ∀ k ∈ region, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      ∀ w ∈ (gateAt C k).inputs, w ∈ src ∨ (N ≤ w ∧ w - N ∈ region) ∨ w ∈ entry) :
    ∀ w, N ≤ w → w - N ∈ region → val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
    rw [Nat.add_sub_cancel_left] at h2
    have hj : j < C.size := Finset.mem_range.1 (hreg h2)
    rw [val_gate C x N hx hR j hj, val_gate C y N hy hR j hj]
    obtain ⟨hop, hin⟩ := hgates j h2
    apply op_mono _ hop
    intro i hi hxi
    rcases hin i hi with hs | hs | hs
    · obtain ⟨hlt, heq⟩ := hsrc i hs
      rw [val_lt C x i (by omega)] at hxi
      rw [val_lt C y i (by omega), ← heq]; exact hxi
    · exact ih i (by have := hR j hj i hi; omega) hs.1 hs.2 hxi
    · exact hent i hs hxi

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = (decide (i = u.val) || decide (i = n + v.val)) := by
  unfold oneEach
  by_cases h : i < n
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h)]
    have h1 : i ≠ n + v.val := by omega
    simp [h, h1, Fin.ext_iff]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using h)]
    have h1 : i ≠ u.val := by have := u.isLt; omega
    by_cases h2 : i - n < m
    · simp [h2, h1, Fin.ext_iff]; omega
    · have h3 : i ≠ n + v.val := by have := v.isLt; omega
      simp [h2, h1, h3]

theorem oneEach_row {n m : ℕ} (u r : Fin n) (v : Fin m) :
    (oneEach u v).getD r.val false = decide (r = u) := by
  rw [oneEach_getD]
  have : r.val ≠ n + v.val := by omega
  simp [this, Fin.ext_iff]

theorem oneEach_col {n m : ℕ} (u : Fin n) (v c : Fin m) :
    (oneEach u v).getD (n + c.val) false = decide (c = v) := by
  rw [oneEach_getD]
  have : n + c.val ≠ u.val := by omega
  simp [this, Fin.ext_iff]

theorem dec_congr (entry : Finset ℕ) (f g : ℕ → Bool) (h : ∀ w ∈ entry, f w = g w) :
    decide (∃ w ∈ entry, f w = true) = decide (∃ w ∈ entry, g w = true) :=
  decide_eq_decide.2 ⟨fun ⟨w, hw, h'⟩ => ⟨w, hw, h w hw ▸ h'⟩,
    fun ⟨w, hw, h'⟩ => ⟨w, hw, (h w hw).symm ▸ h'⟩⟩

theorem ent_imp (entry : Finset ℕ) (he : entry.card ≤ 1) (f g : ℕ → Bool)
    (h : decide (∃ w ∈ entry, f w = true) = true → decide (∃ w ∈ entry, g w = true) = true) :
    ∀ w ∈ entry, f w = true → g w = true := by
  intro w hw hf
  obtain ⟨w', hw', hg⟩ := of_decide_eq_true (h (decide_eq_true ⟨w, hw, hf⟩))
  rw [Finset.card_le_one.1 he w hw w' hw']; exact hg

/-- The counting core. Rows of `R` reach the rest only through `top`; on a column outside `B` the
entry bit `ent` does not depend on the row, and `top` is monotone in it. Then `R` has at most
three rows, and at most two when the entry bit is always false. -/
theorem count3 {α β : Type} [Fintype β] [DecidableEq β] (d : ℕ) (H : α → β → Bool)
    (R : Finset α) (B : Finset β) (top ent : α → β → Bool)
    (hdist : ∀ u ∈ R, ∀ u' ∈ R, u ≠ u' →
      d ≤ (Finset.univ.filter (fun v => H u v ≠ H u' v)).card)
    (hB : B.card < d)
    (hout : ∀ u ∈ R, ∀ u' ∈ R, ∀ v, v ∉ B → top u v = top u' v → H u v = H u' v)
    (hent : ∀ u ∈ R, ∀ u' ∈ R, ∀ v, v ∉ B → ent u v = ent u' v)
    (hmono : ∀ u ∈ R, ∀ v v', v ∉ B → v' ∉ B → (ent u v = true → ent u v' = true) →
      top u v = true → top u v' = true) :
    R.card ≤ 3 ∧ ((∀ u ∈ R, ∀ v, v ∉ B → ent u v = false) → R.card ≤ 2) := by
  classical
  let c : Bool → α → Bool := fun b u => decide (∃ v, v ∉ B ∧ ent u v = b ∧ top u v = true)
  have hK : ∀ u ∈ R, ∀ v, v ∉ B → top u v = c (ent u v) u := by
    intro u hu v hv
    by_cases ht : top u v = true
    · rw [ht]; symm; exact decide_eq_true ⟨v, hv, rfl, ht⟩
    · rw [Bool.not_eq_true] at ht
      rw [ht]; symm
      apply decide_eq_false
      rintro ⟨v', hv', he, ht'⟩
      have := hmono u hu v' v hv' hv (fun h => he ▸ h) ht'
      rw [ht] at this; exact Bool.false_ne_true this
  have hinj : ∀ u ∈ R, ∀ u' ∈ R, c false u = c false u' → c true u = c true u' → u = u' := by
    intro u hu u' hu' h0 h1
    by_contra hne
    have hsub : Finset.univ.filter (fun v => H u v ≠ H u' v) ⊆ B := by
      intro v hv
      rw [Finset.mem_filter] at hv
      by_contra hvB
      apply hv.2
      apply hout u hu u' hu' v hvB
      rw [hK u hu v hvB, hK u' hu' v hvB, ← hent u hu u' hu' v hvB]
      cases ent u v
      · exact h0
      · exact h1
    have h1 := Finset.card_le_card hsub
    have h2 := hdist u hu u' hu' hne
    omega
  let f : α → Bool × Bool := fun u => (c false u, c true u)
  have hfi : Set.InjOn f R := by
    intro u hu u' hu' h
    exact hinj u hu u' hu' (Prod.ext_iff.1 h).1 (Prod.ext_iff.1 h).2
  have two : (∀ u ∈ R, ∀ v, v ∉ B → ent u v = false) → R.card ≤ 2 := by
    intro hE
    have hmap : Set.MapsTo f R (Finset.univ.filter (fun p : Bool × Bool => p.2 = false)) := by
      intro u hu
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      apply decide_eq_false
      rintro ⟨v, hv, he, _⟩
      rw [hE u hu v hv] at he; exact Bool.false_ne_true he
    have := Finset.card_le_card_of_injOn f hmap hfi
    have hc : (Finset.univ.filter (fun p : Bool × Bool => p.2 = false)).card = 2 := by decide
    omega
  refine ⟨?_, two⟩
  by_cases hz : ∃ u0 ∈ R, f u0 = (true, false)
  · obtain ⟨u0, hu0, hf0⟩ := hz
    have h0 : c false u0 = true := (Prod.ext_iff.1 hf0).1
    have h1 : c true u0 = false := (Prod.ext_iff.1 hf0).2
    have hE : ∀ u ∈ R, ∀ v, v ∉ B → ent u v = false := by
      intro u hu v hv
      rw [Bool.eq_false_iff]
      intro he
      rw [hent u hu u0 hu0 v hv] at he
      obtain ⟨v0, hv0, he0, ht0⟩ := of_decide_eq_true h0
      have ht := hmono u0 hu0 v0 v hv0 hv
        (fun h => by rw [he0] at h; exact absurd h Bool.false_ne_true) ht0
      have : c true u0 = true := decide_eq_true ⟨v, hv, he, ht⟩
      rw [h1] at this; exact Bool.false_ne_true this
    have := two hE
    omega
  · have hmap : Set.MapsTo f R (Finset.univ.erase ((true, false) : Bool × Bool)) := by
      intro u hu
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_diff, Set.mem_univ, true_and,
        Set.mem_singleton_iff]
      exact fun h => hz ⟨u, hu, h⟩
    have := Finset.card_le_card_of_injOn f hmap hfi
    have hc : (Finset.univ.erase ((true, false) : Bool × Bool)).card = 3 := by decide
    omega

end PEqualNP.Outside.L_meta_25551_aux

open PEqualNP.Outside.L_meta_25551_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25551 :
    ∀ (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ),
      let raw := n + m
      let sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
      let inside := fun (w : ℕ) => raw ≤ w ∧ w - raw ∈ region
      let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
      (∀ firstRow secondRow : Fin n, firstRow ≠ secondRow → d ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card) →
      (∀ firstCol secondCol : Fin m, firstCol ≠ secondCol → d ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card) →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
      PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → top ∈ region →
      entry.card ≤ 1 → (∀ w ∈ entry, w < raw + top ∧ w ∉ sources ∧ ¬ inside w) →
      (∀ k ∈ region,
        ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
         (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∀ w ∈ (gate k).inputs, w ∈ sources ∨ inside w ∨ w ∈ entry) →
      (∀ k < C.size, k ∉ region → ∀ w ∈ (gate k).inputs,
        w ∉ sources ∧ (inside w → w = raw + top)) →
      C.output ∉ sources → (inside C.output → C.output = raw + top) →
      (B.card < d → R.card ≤ 2 + entry.card) ∧ (R.card < d → B.card ≤ 2 + entry.card) := by
  intro n m d G C R B region entry top raw sources inside gate hrow hcol hR hrep hreg htop
    hecard hentry hgates hout houtput houtside
  have SL : ∀ s ∈ sources, s < raw := by
    intro s hs
    rcases Finset.mem_union.1 hs with h | h
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 h
      have := r.isLt; show r.val < n + m; omega
    · obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 h
      have := c.isLt; show n + c.val < n + m; omega
  have F1 : ∀ x y : List Bool, x.length = raw → y.length = raw →
      (∀ w < raw, w ∉ sources → x.getD w false = y.getD w false) →
      ∀ w ∈ entry, val C x w = val C y w := by
    intro x y hx hy hns w hw
    obtain ⟨h1, h2, h3⟩ := hentry w hw
    refine closure C x y raw hx hy hR (fun w => w ∉ sources ∧ ¬ inside w ∧ w < raw + top) ?_ ?_
      w ⟨h2, h3, h1⟩
    · intro w hw' hg; exact hns w hw' hg.1
    · intro j hj hg
      right
      intro i hi
      have hjr : j ∉ region := fun h =>
        hg.2.1 ⟨Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact h⟩
      obtain ⟨a, b⟩ := hout j hj hjr i hi
      have hlt : i < raw + j := hR j hj i hi
      have hjt : raw + j < raw + top := hg.2.2
      exact ⟨a, fun hin => by have := b hin; omega, by omega⟩
  have F2 : ∀ x y : List Bool, x.length = raw → y.length = raw →
      (∀ w < raw, w ∉ sources → x.getD w false = y.getD w false) →
      val C x (raw + top) = val C y (raw + top) → C.eval x = C.eval y := by
    intro x y hx hy hns htv
    refine closure C x y raw hx hy hR (fun w => w ∉ sources ∧ (inside w → w = raw + top))
      (fun w hw hg => hns w hw hg.1) ?_ C.output ⟨houtput, houtside⟩
    intro j hj hg
    by_cases hjr : j ∈ region
    · left
      have := hg.2 ⟨Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact hjr⟩
      rw [this]; exact htv
    · right; intro i hi; exact hout j hj hjr i hi
  have F3 : ∀ x y : List Bool, x.length = raw → y.length = raw →
      (∀ s ∈ sources, x.getD s false = y.getD s false) →
      (∀ w ∈ entry, val C x w = true → val C y w = true) →
      val C x (raw + top) = true → val C y (raw + top) = true := by
    intro x y hx hy hs he
    exact region_mono C x y raw hx hy hR region entry sources hreg
      (fun s h => ⟨SL s h, hs s h⟩) he hgates (raw + top) (Nat.le_add_right _ _)
      (by rw [Nat.add_sub_cancel_left]; exact htop)
  have NS : ∀ (u u' : Fin n) (v v' : Fin m), (u = u' ∨ (u ∈ R ∧ u' ∈ R)) →
      (v = v' ∨ (v ∈ B ∧ v' ∈ B)) →
      ∀ w < raw, w ∉ sources → (oneEach u v).getD w false = (oneEach u' v').getD w false := by
    intro u u' v v' hu hv w _ hns
    have hr : ∀ r ∈ R, w ≠ r.val := fun r hr h =>
      hns (Finset.mem_union_left _ (Finset.mem_image.2 ⟨r, hr, h.symm⟩))
    have hc : ∀ c ∈ B, w ≠ n + c.val := fun c hc h =>
      hns (Finset.mem_union_right _ (Finset.mem_image.2 ⟨c, hc, h.symm⟩))
    rw [oneEach_getD, oneEach_getD]
    have a : decide (w = u.val) = decide (w = u'.val) := by
      rcases hu with rfl | ⟨hu, hu'⟩
      · rfl
      · rw [decide_eq_false (hr u hu), decide_eq_false (hr u' hu')]
    have b : decide (w = n + v.val) = decide (w = n + v'.val) := by
      rcases hv with rfl | ⟨hv, hv'⟩
      · rfl
      · rw [decide_eq_false (hc v hv), decide_eq_false (hc v' hv')]
    rw [a, b]
  have SA : ∀ (u u' : Fin n) (v v' : Fin m), (u = u' ∨ (u ∉ R ∧ u' ∉ R)) →
      (v = v' ∨ (v ∉ B ∧ v' ∉ B)) →
      ∀ s ∈ sources, (oneEach u v).getD s false = (oneEach u' v').getD s false := by
    intro u u' v v' hu hv s hs
    rcases Finset.mem_union.1 hs with h | h
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 h
      rw [oneEach_row, oneEach_row]
      rcases hu with rfl | ⟨hu, hu'⟩
      · rfl
      · rw [decide_eq_false (fun e : r = u => hu (e ▸ hr)), decide_eq_false (fun e : r = u' => hu' (e ▸ hr))]
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
      rw [oneEach_col, oneEach_col]
      rcases hv with rfl | ⟨hv, hv'⟩
      · rfl
      · rw [decide_eq_false (fun e : c = v => hv (e ▸ hc)), decide_eq_false (fun e : c = v' => hv' (e ▸ hc))]
  have hEmp : entry.card = 0 → ∀ (u : Fin n) (v : Fin m),
      decide (∃ w ∈ entry, val C (oneEach u v) w = true) = false := by
    intro h0 u v
    rw [Finset.card_eq_zero.1 h0]
    apply decide_eq_false
    rintro ⟨w, hw, _⟩
    exact absurd hw (Finset.notMem_empty w)
  refine ⟨fun hB => ?_, fun hRc => ?_⟩
  · obtain ⟨h3, h2⟩ := count3 d G R B (fun u v => val C (oneEach u v) (raw + top))
      (fun u v => decide (∃ w ∈ entry, val C (oneEach u v) w = true))
      (fun u _ u' _ hne => hrow u u' hne) hB
      (fun u hu u' hu' v _ ht => (hrep u v).symm.trans ((F2 _ _ (oneEach_length u v)
        (oneEach_length u' v) (NS u u' v v (Or.inr ⟨hu, hu'⟩) (Or.inl rfl)) ht).trans (hrep u' v)))
      (fun u hu u' hu' v _ => dec_congr entry _ _ (F1 _ _ (oneEach_length u v)
        (oneEach_length u' v) (NS u u' v v (Or.inr ⟨hu, hu'⟩) (Or.inl rfl))))
      (fun u _ v v' hv hv' himp => F3 _ _ (oneEach_length u v) (oneEach_length u v')
        (SA u u v v' (Or.inl rfl) (Or.inr ⟨hv, hv'⟩)) (ent_imp entry hecard _ _ himp))
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hecard with h0 | h1
    · rw [h0]; exact h2 (fun u _ v _ => hEmp h0 u v)
    · rw [h1]; exact h3
  · obtain ⟨h3, h2⟩ := count3 d (fun c r => G r c) B R
      (fun c r => val C (oneEach r c) (raw + top))
      (fun c r => decide (∃ w ∈ entry, val C (oneEach r c) w = true))
      (fun v _ v' _ hne => hcol v v' hne) hRc
      (fun v hv v' hv' u _ ht => (hrep u v).symm.trans ((F2 _ _ (oneEach_length u v)
        (oneEach_length u v') (NS u u v v' (Or.inl rfl) (Or.inr ⟨hv, hv'⟩)) ht).trans (hrep u v')))
      (fun v hv v' hv' u _ => dec_congr entry _ _ (F1 _ _ (oneEach_length u v)
        (oneEach_length u v') (NS u u v v' (Or.inl rfl) (Or.inr ⟨hv, hv'⟩))))
      (fun v _ u u' hu hu' himp => F3 _ _ (oneEach_length u v) (oneEach_length u' v)
        (SA u u' v v (Or.inr ⟨hu, hu'⟩) (Or.inl rfl)) (ent_imp entry hecard _ _ himp))
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hecard with h0 | h1
    · rw [h0]; exact h2 (fun v _ u _ => hEmp h0 u v)
    · rw [h1]; exact h3
