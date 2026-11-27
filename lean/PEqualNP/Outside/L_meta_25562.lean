import PEqualNP.Defs

-- L-meta-25562: each subtree of the read-once tree is a private AND/OR region whose one entry wire,
-- if any, is the outside operand, so by the L-meta-25551 argument (inlined below) a subtree with
-- fewer than six columns has at most 2 + e rows and vice versa. By induction on the tree every
-- subtree has at most 2 + e rows and columns; children read disjoint entries, so at most five.

namespace PEqualNP.Outside.L_meta_25562_aux
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


-- the private-region bound, L-meta-25551 (same statement and proof as its own file)
theorem l25551 :
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

/-! ### Subtrees of a read-once AND/OR region, and the bound by induction on the tree -/

def RD {n : ℕ} (R : Finset (Fin n)) (D : Finset ℕ) : Finset (Fin n) := R.filter (fun r => r.val ∈ D)

def BD {m : ℕ} (n : ℕ) (B : Finset (Fin m)) (D : Finset ℕ) : Finset (Fin m) :=
  B.filter (fun c => n + c.val ∈ D)

def regD (N : ℕ) (region D : Finset ℕ) : Finset ℕ := region.filter (fun k => N + k ∈ D)

def ED (C : Circuit) (N : ℕ) (region E D : Finset ℕ) : Finset ℕ :=
  E.filter (fun e => ∃ k ∈ regD N region D, e ∈ (gateAt C k).inputs)

/-- `D` is the wire set of a subtree with top `w`: tree wires, at most `w`, closed under the
operands of its gates (up to entry wires), and every wire but the top is read by one of its gates. -/
def Node (C : Circuit) (N : ℕ) (region E W D : Finset ℕ) (w : ℕ) : Prop :=
  D ⊆ W ∧ (∀ x ∈ D, x ≤ w) ∧
  (∀ k ∈ region, N + k ∈ D → ∀ i ∈ (gateAt C k).inputs, i ∈ D ∨ i ∈ E) ∧
  (∀ x ∈ D, x ≠ w → ∃ k ∈ region, N + k ∈ D ∧ x ∈ (gateAt C k).inputs)

theorem reads_ge (C : Circuit) (S : Finset ℕ) (x k : ℕ) (hk : k ∈ S) :
    (gateAt C k).inputs.count x ≤ readsIn C S x :=
  Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count x) (fun _ _ => Nat.zero_le _) hk

theorem reads_pos (C : Circuit) (S : Finset ℕ) (x k : ℕ) (hk : k ∈ S)
    (hx : x ∈ (gateAt C k).inputs) : 1 ≤ readsIn C S x :=
  le_trans (List.count_pos_iff.2 hx) (reads_ge C S x k hk)

theorem reads_uniq (C : Circuit) (S : Finset ℕ) (x : ℕ) (h1 : readsIn C S x ≤ 1) (k k' : ℕ)
    (hk : k ∈ S) (hk' : k' ∈ S) (hx : x ∈ (gateAt C k).inputs)
    (hx' : x ∈ (gateAt C k').inputs) : k = k' := by
  by_contra hne
  have hsub : ({k, k'} : Finset ℕ) ⊆ S := by
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hk
    · rw [Finset.mem_singleton.1 hj]; exact hk'
  have h2 : (gateAt C k).inputs.count x + (gateAt C k').inputs.count x ≤ readsIn C S x := by
    rw [← Finset.sum_pair (f := fun j => (gateAt C j).inputs.count x) hne]
    exact Finset.sum_le_sum_of_subset hsub
  have := List.count_pos_iff.2 hx
  have := List.count_pos_iff.2 hx'
  omega

theorem reads_exists (C : Circuit) (S : Finset ℕ) (x : ℕ) (h : readsIn C S x ≠ 0) :
    ∃ k ∈ S, x ∈ (gateAt C k).inputs := by
  unfold readsIn at h
  obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨k, hk, List.count_pos_iff.1 (Nat.pos_of_ne_zero hne)⟩

/-- Every subtree has at most `2 + e` rows and columns, `e` the entry wires it reads; children
together have at most `4 + |E| < d` on each side, so the private-region bound applies. -/
theorem core (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit) (R : Finset (Fin n))
    (B : Finset (Fin m)) (region E W : Finset ℕ) (root : ℕ)
    (hWd : W = (R.image (fun r => r.val) ∪ B.image (fun c => n + c.val)) ∪
      region.image (fun k => n + m + k))
    (hrow : ∀ a b : Fin n, a ≠ b → d ≤ (Finset.univ.filter (fun col => G a col ≠ G b col)).card)
    (hcol : ∀ i j : Fin m, i ≠ j → d ≤ (Finset.univ.filter (fun row => G row i ≠ G row j)).card)
    (hR : ReadsBack (n + m) C) (hrep : Represents G C) (hreg : region ⊆ Finset.range C.size)
    (hE : E.card ≤ 1) (hd : 4 + E.card < d) (hEW : ∀ e ∈ E, e ∉ W)
    (hEr : ∀ e ∈ E, readsIn C region e = 1)
    (hgates : ∀ k ∈ region, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length = 2 ∧ ∀ w ∈ (gateAt C k).inputs, w ∈ W ∨ w ∈ E)
    (hroot : root ∈ W) (hroot0 : readsIn C region root = 0)
    (hWr : ∀ w ∈ W, w ≠ root → readsIn C region w = 1 ∧
      readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w) :
    R.card + B.card ≤ 4 + 2 * E.card := by
  classical
  have rowW : ∀ r ∈ R, r.val ∈ W := fun r hr => by
    rw [hWd]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hr))
  have colW : ∀ c ∈ B, n + c.val ∈ W := fun c hc => by
    rw [hWd]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc))
  have gateW : ∀ k ∈ region, n + m + k ∈ W := fun k hk => by
    rw [hWd]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
  have Wcases : ∀ x ∈ W, (∃ r ∈ R, x = r.val) ∨ (∃ c ∈ B, x = n + c.val) ∨
      (∃ k ∈ region, x = n + m + k) := by
    intro x hx
    rw [hWd] at hx
    rcases Finset.mem_union.1 hx with h | h
    · rcases Finset.mem_union.1 h with h | h
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 h; exact Or.inl ⟨r, hr, rfl⟩
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h; exact Or.inr (Or.inl ⟨c, hc, rfl⟩)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h; exact Or.inr (Or.inr ⟨k, hk, rfl⟩)
  have inR : ∀ k ∈ region, k < C.size := fun k hk => Finset.mem_range.1 (hreg hk)
  have rb : ∀ k ∈ region, ∀ x ∈ (gateAt C k).inputs, x < n + m + k :=
    fun k hk x hx => hR k (inR k hk) x hx
  have notroot : ∀ x, ∀ k ∈ region, x ∈ (gateAt C k).inputs → x ≠ root := by
    intro x k hk hx h
    have := reads_pos C region x k hk hx
    rw [h, hroot0] at this; omega
  have uLoc : ∀ x ∈ W, ∀ k ∈ region, ∀ k' ∈ region, x ∈ (gateAt C k).inputs →
      x ∈ (gateAt C k').inputs → k = k' := by
    intro x hx k hk k' hk' h1 h2
    exact reads_uniq C region x (hWr x hx (notroot x k hk h1)).1.le k k' hk hk' h1 h2
  have uAll : ∀ x ∈ W, ∀ k ∈ region, ∀ k', k' < C.size → x ∈ (gateAt C k).inputs →
      x ∈ (gateAt C k').inputs → k' = k := by
    intro x hx k hk k' hk' h1 h2
    exact reads_uniq C (Finset.range C.size) x (hWr x hx (notroot x k hk h1)).2.1.le k' k
      (Finset.mem_range.2 hk') (hreg hk) h2 h1
  have uE : ∀ e ∈ E, ∀ k ∈ region, ∀ k' ∈ region, e ∈ (gateAt C k).inputs →
      e ∈ (gateAt C k').inputs → k = k' := by
    intro e he k hk k' hk' h1 h2
    exact reads_uniq C region e (hEr e he).le k k' hk hk' h1 h2
  -- one subtree is a private region with at most one entry wire
  have step : ∀ (D : Finset ℕ) (kw : ℕ), kw ∈ region → n + m + kw ∈ D →
      Node C (n + m) region E W D (n + m + kw) →
      ((BD n B D).card < d → (RD R D).card ≤ 2 + (ED C (n + m) region E D).card) ∧
      ((RD R D).card < d → (BD n B D).card ≤ 2 + (ED C (n + m) region E D).card) := by
    intro D kw hkw hwD hN
    obtain ⟨hDW, hDle, hP2, hP3⟩ := hN
    have upD : ∀ x ∈ D, x ≠ n + m + kw → ∀ k < C.size, x ∈ (gateAt C k).inputs →
        k ∈ regD (n + m) region D := by
      intro x hx hne k hk hxk
      obtain ⟨k', hk', hk'D, hxk'⟩ := hP3 x hx hne
      rw [uAll x (hDW hx) k' hk' k hk hxk' hxk]
      exact Finset.mem_filter.2 ⟨hk', hk'D⟩
    have srcD : ∀ w ∈ (RD R D).image (fun r => r.val) ∪ (BD n B D).image (fun c => n + c.val),
        w ∈ D ∧ w < n + m := by
      intro w hw
      rcases Finset.mem_union.1 hw with h | h
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 h
        exact ⟨(Finset.mem_filter.1 hr).2, by have := r.isLt; omega⟩
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
        exact ⟨(Finset.mem_filter.1 hc).2, by have := c.isLt; omega⟩
    have insD : ∀ w, n + m ≤ w → w - (n + m) ∈ regD (n + m) region D → w ∈ D := by
      intro w h1 h2
      have := (Finset.mem_filter.1 h2).2
      rwa [Nat.add_sub_cancel' h1] at this
    have key := l25551 n m d G C (RD R D) (BD n B D) (regD (n + m) region D)
      (ED C (n + m) region E D) kw
    have h1 : regD (n + m) region D ⊆ Finset.range C.size := (Finset.filter_subset _ _).trans hreg
    have h2 : kw ∈ regD (n + m) region D := Finset.mem_filter.2 ⟨hkw, hwD⟩
    have h3 : (ED C (n + m) region E D).card ≤ 1 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans hE
    have h4 : ∀ w ∈ ED C (n + m) region E D, w < n + m + kw ∧
        w ∉ (RD R D).image (fun r => r.val) ∪ (BD n B D).image (fun c => n + c.val) ∧
        ¬ (n + m ≤ w ∧ w - (n + m) ∈ regD (n + m) region D) := by
      intro e he
      obtain ⟨heE, k, hk, hek⟩ := Finset.mem_filter.1 he
      obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
      refine ⟨?_, fun hs => hEW e heE (hDW (srcD e hs).1),
        fun hi => hEW e heE (hDW (insD e hi.1 hi.2))⟩
      have := rb k hk1 e hek
      have := hDle _ hk2
      omega
    have h5 : ∀ k ∈ regD (n + m) region D,
        ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
        ∀ w ∈ (gateAt C k).inputs,
          w ∈ (RD R D).image (fun r => r.val) ∪ (BD n B D).image (fun c => n + c.val) ∨
          (n + m ≤ w ∧ w - (n + m) ∈ regD (n + m) region D) ∨ w ∈ ED C (n + m) region E D := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
      refine ⟨(hgates k hk1).1, fun i hi => ?_⟩
      rcases hP2 k hk1 hk2 i hi with hiD | hiE
      · rcases Wcases i (hDW hiD) with ⟨r, hr, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨k', hk', rfl⟩
        · exact Or.inl (Finset.mem_union_left _
            (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hr, hiD⟩)))
        · exact Or.inl (Finset.mem_union_right _
            (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hc, hiD⟩)))
        · refine Or.inr (Or.inl ⟨Nat.le_add_right _ _, ?_⟩)
          rw [Nat.add_sub_cancel_left]; exact Finset.mem_filter.2 ⟨hk', hiD⟩
      · exact Or.inr (Or.inr (Finset.mem_filter.2 ⟨hiE, k, hk, hi⟩))
    have h6 : ∀ k < C.size, k ∉ regD (n + m) region D → ∀ w ∈ (gateAt C k).inputs,
        w ∉ (RD R D).image (fun r => r.val) ∪ (BD n B D).image (fun c => n + c.val) ∧
        (n + m ≤ w ∧ w - (n + m) ∈ regD (n + m) region D → w = n + m + kw) := by
      intro k hk hkn w hw
      refine ⟨fun hs => ?_, fun hi => ?_⟩
      · obtain ⟨hwD', hlt⟩ := srcD w hs
        exact hkn (upD w hwD' (by omega) k hk hw)
      · by_contra hne
        exact hkn (upD w (insD w hi.1 hi.2) hne k hk hw)
    have outOK : ∀ w ∈ D, w ≠ n + m + kw → C.output ≠ w := by
      intro w hw hne
      obtain ⟨k', hk', _, hxk'⟩ := hP3 w hw hne
      exact (hWr w (hDW hw) (notroot w k' hk' hxk')).2.2
    have h7 : C.output ∉
        (RD R D).image (fun r => r.val) ∪ (BD n B D).image (fun c => n + c.val) := by
      intro hs
      obtain ⟨hoD, hlt⟩ := srcD _ hs
      exact outOK _ hoD (by omega) rfl
    have h8 : n + m ≤ C.output ∧ C.output - (n + m) ∈ regD (n + m) region D →
        C.output = n + m + kw := by
      intro hi
      by_contra hne
      exact outOK _ (insD _ hi.1 hi.2) hne rfl
    exact key hrow hcol hR hrep h1 h2 h3 h4 h5 h6 h7 h8
  have single : ∀ x ∈ W, x < n + m → ∃ D : Finset ℕ, x ∈ D ∧ Node C (n + m) region E W D x ∧
      (RD R D).card ≤ 2 + (ED C (n + m) region E D).card ∧
      (BD n B D).card ≤ 2 + (ED C (n + m) region E D).card := by
    intro x hx hlt
    refine ⟨{x}, Finset.mem_singleton_self x,
      ⟨Finset.singleton_subset_iff.2 hx, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro y hy; rw [Finset.mem_singleton.1 hy]
    · intro k _ hk
      rw [Finset.mem_singleton] at hk
      exact absurd hk (by omega)
    · intro y hy hne; exact absurd (Finset.mem_singleton.1 hy) hne
    · have : (RD R {x}).card ≤ 1 := Finset.card_le_one.2 (fun a ha b hb => by
        have h1 := (Finset.mem_filter.1 ha).2
        have h2 := (Finset.mem_filter.1 hb).2
        rw [Finset.mem_singleton] at h1 h2
        exact Fin.ext (h1.trans h2.symm))
      omega
    · have : (BD n B {x}).card ≤ 1 := Finset.card_le_one.2 (fun a ha b hb => by
        have h1 := (Finset.mem_filter.1 ha).2
        have h2 := (Finset.mem_filter.1 hb).2
        rw [Finset.mem_singleton] at h1 h2
        exact Fin.ext (by omega))
      omega
  have build : ∀ w, w ∈ W → ∃ D : Finset ℕ, w ∈ D ∧ Node C (n + m) region E W D w ∧
      (RD R D).card ≤ 2 + (ED C (n + m) region E D).card ∧
      (BD n B D).card ≤ 2 + (ED C (n + m) region E D).card := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      rcases Wcases w hw with ⟨r, hr, hwr⟩ | ⟨c, hc, hwc⟩ | ⟨kw, hkw, hwk⟩
      · exact single w hw (by have := r.isLt; omega)
      · exact single w hw (by have := c.isLt; omega)
      subst hwk
      obtain ⟨hop, hlen, hin⟩ := hgates kw hkw
      obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
      have ha : a ∈ (gateAt C kw).inputs := by rw [hab]; simp
      have hb : b ∈ (gateAt C kw).inputs := by rw [hab]; simp
      have hneab : a ≠ b := by
        intro h
        subst h
        have h2 : 2 ≤ readsIn C region a := by
          have := reads_ge C region a kw hkw
          rw [hab] at this; simpa using this
        rcases hin a ha with haW | haE
        · have := (hWr a haW (notroot a kw hkw ha)).1; omega
        · have := hEr a haE; omega
      have child : ∀ c, c ∈ (gateAt C kw).inputs → ∃ Dc : Finset ℕ, (c ∈ W → c ∈ Dc) ∧
          Node C (n + m) region E W Dc c ∧
          (RD R Dc).card ≤ 2 + (ED C (n + m) region E Dc).card ∧
          (BD n B Dc).card ≤ 2 + (ED C (n + m) region E Dc).card := by
        intro c hc
        by_cases hcW : c ∈ W
        · obtain ⟨Dc, h1, h2, h3⟩ := ih c (rb kw hkw c hc) hcW
          exact ⟨Dc, fun _ => h1, h2, h3⟩
        · refine ⟨∅, fun h => absurd h hcW, ⟨Finset.empty_subset _, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
            simp [RD, BD]
      obtain ⟨Da, haDa, hNa, hRa, hBa⟩ := child a ha
      obtain ⟨Db, hbDb, hNb, hRb, hBb⟩ := child b hb
      have hra := rb kw hkw a ha
      have hrb := rb kw hkw b hb
      have hdisj : Da ∩ Db = ∅ := by
        by_contra hne
        obtain ⟨x, hx, hmax⟩ :=
          Finset.exists_max_image (Da ∩ Db) id (Finset.nonempty_iff_ne_empty.2 hne)
        obtain ⟨hxa, hxb⟩ := Finset.mem_inter.1 hx
        by_cases hxa' : x = a
        · rw [hxa'] at hxb
          obtain ⟨k, hk, hkD, hxk⟩ := hNb.2.2.2 a hxb hneab
          have hk' := uLoc a (hNb.1 hxb) k hk kw hkw hxk ha
          rw [hk'] at hkD
          have := hNb.2.1 _ hkD
          omega
        by_cases hxb' : x = b
        · rw [hxb'] at hxa
          obtain ⟨k, hk, hkD, hxk⟩ := hNa.2.2.2 b hxa (Ne.symm hneab)
          have hk' := uLoc b (hNa.1 hxa) k hk kw hkw hxk hb
          rw [hk'] at hkD
          have := hNa.2.1 _ hkD
          omega
        obtain ⟨k1, hk1, hk1D, hxk1⟩ := hNa.2.2.2 x hxa hxa'
        obtain ⟨k2, hk2, hk2D, hxk2⟩ := hNb.2.2.2 x hxb hxb'
        have hk12 := uLoc x (hNa.1 hxa) k1 hk1 k2 hk2 hxk1 hxk2
        rw [← hk12] at hk2D
        have hle : n + m + k1 ≤ x := hmax _ (Finset.mem_inter.2 ⟨hk1D, hk2D⟩)
        have := rb k1 hk1 x hxk1
        omega
      have hND : Node C (n + m) region E W (insert (n + m + kw) (Da ∪ Db)) (n + m + kw) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hw
          rcases Finset.mem_union.1 hx with hx | hx
          · exact hNa.1 hx
          · exact hNb.1 hx
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact le_refl _
          rcases Finset.mem_union.1 hx with hx | hx
          · have := hNa.2.1 x hx; omega
          · have := hNb.2.1 x hx; omega
        · intro k hk hkD i hi
          rcases Finset.mem_insert.1 hkD with hkw' | hkD
          · have hk' : k = kw := by omega
            rw [hk'] at hi
            have hi' : i = a ∨ i = b := by rw [hab] at hi; simpa using hi
            rcases hin i hi with hiW | hiE
            · rcases hi' with rfl | rfl
              · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_union_left _ (haDa hiW)))
              · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_union_right _ (hbDb hiW)))
            · exact Or.inr hiE
          rcases Finset.mem_union.1 hkD with hkD | hkD
          · rcases hNa.2.2.1 k hk hkD i hi with h | h
            · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
            · exact Or.inr h
          · rcases hNb.2.2.1 k hk hkD i hi with h | h
            · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
            · exact Or.inr h
        · intro x hx hne
          rcases Finset.mem_insert.1 hx with h | hx
          · exact absurd h hne
          rcases Finset.mem_union.1 hx with hx | hx
          · by_cases hxa : x = a
            · rw [hxa]; exact ⟨kw, hkw, Finset.mem_insert_self _ _, ha⟩
            · obtain ⟨k, hk, hkD, hxk⟩ := hNa.2.2.2 x hx hxa
              exact ⟨k, hk, Finset.mem_insert_of_mem (Finset.mem_union_left _ hkD), hxk⟩
          · by_cases hxb : x = b
            · rw [hxb]; exact ⟨kw, hkw, Finset.mem_insert_self _ _, hb⟩
            · obtain ⟨k, hk, hkD, hxk⟩ := hNb.2.2.2 x hx hxb
              exact ⟨k, hk, Finset.mem_insert_of_mem (Finset.mem_union_right _ hkD), hxk⟩
      have hRsub : RD R (insert (n + m + kw) (Da ∪ Db)) ⊆ RD R Da ∪ RD R Db := by
        intro r hr
        have h := Finset.mem_filter.1 hr
        rcases Finset.mem_insert.1 h.2 with h' | h'
        · have := r.isLt; omega
        rcases Finset.mem_union.1 h' with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨h.1, h'⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨h.1, h'⟩)
      have hBsub : BD n B (insert (n + m + kw) (Da ∪ Db)) ⊆ BD n B Da ∪ BD n B Db := by
        intro c hc
        have h := Finset.mem_filter.1 hc
        rcases Finset.mem_insert.1 h.2 with h' | h'
        · have := c.isLt; omega
        rcases Finset.mem_union.1 h' with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨h.1, h'⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨h.1, h'⟩)
      have hEdisj : ED C (n + m) region E Da ∩ ED C (n + m) region E Db = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        obtain ⟨h1, h2⟩ := Finset.mem_inter.1 he
        obtain ⟨heE, k1, hk1, he1⟩ := Finset.mem_filter.1 h1
        obtain ⟨_, k2, hk2, he2⟩ := Finset.mem_filter.1 h2
        obtain ⟨hk1r, hk1D⟩ := Finset.mem_filter.1 hk1
        obtain ⟨hk2r, hk2D⟩ := Finset.mem_filter.1 hk2
        have hk12 := uE e heE k1 hk1r k2 hk2r he1 he2
        rw [← hk12] at hk2D
        have : n + m + k1 ∈ Da ∩ Db := Finset.mem_inter.2 ⟨hk1D, hk2D⟩
        rw [hdisj] at this; exact Finset.notMem_empty _ this
      have hEsum : (ED C (n + m) region E Da).card + (ED C (n + m) region E Db).card ≤ E.card := by
        have := Finset.card_union_add_card_inter (ED C (n + m) region E Da)
          (ED C (n + m) region E Db)
        rw [hEdisj, Finset.card_empty] at this
        have h2 : ED C (n + m) region E Da ∪ ED C (n + m) region E Db ⊆ E :=
          Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        have := Finset.card_le_card h2
        omega
      have cR := (Finset.card_le_card hRsub).trans (Finset.card_union_le _ _)
      have cB := (Finset.card_le_card hBsub).trans (Finset.card_union_le _ _)
      obtain ⟨s1, s2⟩ := step _ kw hkw (Finset.mem_insert_self _ _) hND
      exact ⟨_, Finset.mem_insert_self _ _, hND, s1 (by omega), s2 (by omega)⟩
  obtain ⟨D, hrD, hND, hRb, hBb⟩ := build root hroot
  have compl : ∀ t, ∀ x ∈ W, n + m + C.size - x = t → x ∈ D := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro x hx ht
      by_cases hxr : x = root
      · rw [hxr]; exact hrD
      obtain ⟨k, hk, hxk⟩ := reads_exists C region x (by rw [(hWr x hx hxr).1]; omega)
      have h1 := rb k hk x hxk
      have h2 := inR k hk
      have hkD := ih (n + m + C.size - (n + m + k)) (by omega) (n + m + k) (gateW k hk) rfl
      rcases hND.2.2.1 k hk hkD x hxk with h | h
      · exact h
      · exact absurd hx (hEW x h)
  have allR : R ⊆ RD R D := fun r hr => Finset.mem_filter.2 ⟨hr, compl _ r.val (rowW r hr) rfl⟩
  have allB : B ⊆ BD n B D := fun c hc => Finset.mem_filter.2 ⟨hc, compl _ _ (colW c hc) rfl⟩
  have hED : (ED C (n + m) region E D).card ≤ E.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have := Finset.card_le_card allR
  have := Finset.card_le_card allB
  omega

end PEqualNP.Outside.L_meta_25562_aux

open PEqualNP.Outside.L_meta_25562_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25562 :
    ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (R : Finset (Fin n)) (B : Finset (Fin m)) (region : Finset ℕ) (root entry : ℕ),
      let raw := n + m
      let sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
      let wires := sources ∪ region.image (fun gateIndex => raw + gateIndex)
      let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
      let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
      let allReads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
      (∀ a b : Fin n, a ≠ b → 6 ≤ (Finset.univ.filter (fun col => G a col ≠ G b col)).card) →
      (∀ i j : Fin m, i ≠ j → 6 ≤ (Finset.univ.filter (fun row => G row i ≠ G row j)).card) →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
      PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → root ∈ wires →
      entry ∉ wires → entry < root → localReads entry = 1 →
      (∀ k ∈ region,
        ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
         (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (gate k).inputs.length = 2 ∧ ∀ w ∈ (gate k).inputs, w ∈ wires ∨ w = entry) →
      localReads root = 0 →
      (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ allReads w = 1 ∧ C.output ≠ w) →
      R.card + B.card ≤ 6 := by
  intro n m G C R B region root entry raw sources wires gate localReads allReads hrow hcol hR hrep
    hreg hroot hentW hlt hentR hgates hroot0 hW
  have := core n m 6 G C R B region {entry} wires root rfl hrow hcol hR hrep hreg (by simp)
    (by simp) (fun e he => by rw [Finset.mem_singleton.1 he]; exact hentW)
    (fun e he => by rw [Finset.mem_singleton.1 he]; exact hentR)
    (fun k hk => ⟨(hgates k hk).1, (hgates k hk).2.1, fun w hw => by
      rcases (hgates k hk).2.2 w hw with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.2 h)⟩)
    hroot hroot0 hW
  simpa using this
