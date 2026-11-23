import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem val_big {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (h : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

theorem val_append {n : ℕ} (gs hs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (h : i < n + gs.length) : val (gs ++ hs) x i = val gs x i := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, val_snoc, if_neg (by simp only [List.length_append]; omega), ih]

theorem val_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val gs x i = x ⟨i, h⟩ := by
  have := val_append [] gs x i (by simp; omega)
  simp only [List.nil_append] at this
  rw [this, val_nil, dif_pos h]

theorem val_take {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (t i : ℕ) (ht : t ≤ gs.length)
    (h : i < n + t) : val (gs.take t) x i = val gs x i := by
  conv_rhs => rw [← List.take_append_drop t gs]
  rw [val_append _ _ _ _ (by rw [List.length_take]; omega)]

theorem val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (t : ℕ) (ht : t < gs.length) :
    val gs x (n + t) = gs[t].op.eval (gs[t].inputs.map fun j => val (gs.take t) x j) := by
  have h1 : gs.take (t + 1) = gs.take t ++ [gs[t]] := List.take_succ_eq_append_getElem ht
  rw [← val_take gs x (t + 1) (n + t) (by omega) (by omega), h1, val_snoc,
    if_pos (by rw [List.length_take]; omega)]

theorem op_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (hfg : ∀ j ∈ l, f j = true → g j = true)
    (h : op.eval (l.map f) = true) : op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at h ⊢
    exact fun j hj => hfg j hj (h j hj)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at h ⊢
    obtain ⟨j, hj, hf⟩ := h
    exact ⟨j, hj, hfg j hj hf⟩

theorem op_split (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (hf : op.eval (l.map f) = true) (hg : op.eval (l.map g) = false) :
    ∃ j ∈ l, f j = true ∧ g j = false := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, List.all_eq_false,
      Function.comp_apply, id_eq] at hf hg
    obtain ⟨j, hj, hgj⟩ := hg
    exact ⟨j, hj, hf j hj, by simpa using hgj⟩
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, List.any_eq_false,
      Function.comp_apply, id_eq] at hf hg
    obtain ⟨j, hj, hfj⟩ := hf
    exact ⟨j, hj, hfj, by simpa using hg j hj⟩

theorem val_mono {n : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ a, x a = true → y a = true) (i : ℕ)
    (h : val gs x i = true) : val gs y i = true := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    rw [val_nil] at h ⊢
    split_ifs at h ⊢ with hi
    · exact hxy _ h
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hg g' (by simp [hg']))
    rw [val_snoc] at h ⊢
    split_ifs at h ⊢ with hi
    · exact op_mono g.op (hg g (by simp)) g.inputs _ _ (fun j _ => ih' j) h
    · exact ih' i h

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Zs {n : ℕ} (gs : List Gate) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun a => val gs (eof a) j = true

def Priv {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (j : ℕ) : Prop :=
  Zs (n := n) gs j ⊆ S ∧ 2 ≤ (Zs (n := n) gs j).card

def RealIn (n : ℕ) (gs : List Gate) (p j : ℕ) : Prop :=
  ∃ t, ∃ ht : t < gs.length, p = n + t ∧ j ∈ (gs[t]).inputs ∧ j < p

inductive InK {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (i : ℕ) : ℕ → Prop
  | base : Priv gs S i → InK gs S i i
  | step {p j : ℕ} : InK gs S i p → RealIn n gs p j → Priv gs S j → InK gs S i j

theorem InK_priv {n : ℕ} {gs : List Gate} {S : Finset (Fin n)} {i p : ℕ}
    (h : InK gs S i p) : Priv gs S p := by
  cases h with
  | base h => exact h
  | step _ _ h => exact h

theorem priv_range {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (p : ℕ) (h : Priv gs S p) :
    n ≤ p ∧ p < n + gs.length := by
  obtain ⟨-, h2⟩ := h
  constructor
  · by_contra hp
    push_neg at hp
    have hs : Zs (n := n) gs p ⊆ {⟨p, hp⟩} := by
      intro a ha
      simp only [Zs, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [val_input gs _ p hp] at ha
      simp only [eof, decide_eq_true_eq] at ha
      simp [← ha]
    have := Finset.card_le_card hs
    simp at this
    omega
  · by_contra hp
    push_neg at hp
    have hs : Zs (n := n) gs p = ∅ := by
      ext a
      simp [Zs, val_big gs _ p hp]
    rw [hs] at h2
    simp at h2

theorem realIn_lt {n : ℕ} {gs : List Gate} {p j : ℕ} (h : RealIn n gs p j) :
    j < p ∧ p < n + gs.length := by
  obtain ⟨t, ht, rfl, -, hj⟩ := h
  exact ⟨hj, by omega⟩

open Classical in
noncomputable def K {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (i : ℕ) : Finset ℕ :=
  (Finset.range (n + gs.length)).filter fun p => InK gs S i p

open Classical in
noncomputable def Ex {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (i : ℕ) : Finset ℕ :=
  (Finset.range (n + gs.length)).filter fun j =>
    ¬ Priv gs S j ∧ ∃ p, InK gs S i p ∧ RealIn n gs p j

open Classical in
noncomputable def Inp (n : ℕ) (gs : List Gate) (p : ℕ) : Finset ℕ :=
  (Finset.range (n + gs.length)).filter fun j => RealIn n gs p j

theorem mem_K {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (i p : ℕ) :
    p ∈ K gs S i ↔ InK gs S i p := by
  classical
  simp only [K, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(priv_range gs S p (InK_priv h)).2, h⟩

theorem mem_Ex {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (i j : ℕ) :
    j ∈ Ex gs S i ↔ ¬ Priv gs S j ∧ ∃ p, InK gs S i p ∧ RealIn n gs p j := by
  classical
  simp only [Ex, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hh := h
    obtain ⟨-, p, -, hr⟩ := hh
    have := realIn_lt hr
    exact ⟨by omega, h⟩

theorem mem_Inp (n : ℕ) (gs : List Gate) (p j : ℕ) :
    j ∈ Inp n gs p ↔ RealIn n gs p j := by
  classical
  simp only [Inp, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have := realIn_lt h
    exact ⟨by omega, h⟩

theorem Inp_card {n : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length = 2) (p : ℕ) :
    (Inp n gs p).card ≤ 2 := by
  classical
  by_cases hp : ∃ t, ∃ _ : t < gs.length, p = n + t
  · obtain ⟨t, ht, rfl⟩ := hp
    have hsub : Inp n gs (n + t) ⊆ (gs[t]).inputs.toFinset := by
      intro j hj
      obtain ⟨t', ht', he, hj', -⟩ := (mem_Inp n gs _ j).mp hj
      have htt : t' = t := by omega
      subst htt
      exact List.mem_toFinset.mpr hj'
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ (gs[t]).inputs.length := List.toFinset_card_le _
      _ = 2 := hg _ (List.getElem_mem ht)
  · have hempty : Inp n gs p = ∅ := by
      ext j
      rw [mem_Inp]
      simp only [Finset.notMem_empty, iff_false]
      rintro ⟨t, ht, he, -⟩
      exact hp ⟨t, ht, he⟩
    rw [hempty]
    simp

theorem ex_card {n : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length = 2)
    (S : Finset (Fin n)) (i : ℕ) (hi : Priv gs S i) :
    (Ex gs S i).card ≤ (K gs S i).card + 1 := by
  classical
  have hiK : i ∈ K gs S i := (mem_K gs S i i).mpr (InK.base hi)
  have hdisj : Disjoint ((K gs S i).erase i) (Ex gs S i) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    have := (mem_K gs S i p).mp (Finset.mem_of_mem_erase hp)
    exact ((mem_Ex gs S i p).mp hp').1 (InK_priv this)
  have hsub : (K gs S i).erase i ∪ Ex gs S i ⊆ (K gs S i).biUnion (Inp n gs) := by
    intro j hj
    rw [Finset.mem_biUnion]
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
      have hk := (mem_K gs S i j).mp hj
      cases hk with
      | base _ => exact absurd rfl hne
      | step hp hr _ => exact ⟨_, (mem_K gs S i _).mpr hp, (mem_Inp n gs _ _).mpr hr⟩
    · obtain ⟨-, p, hp, hr⟩ := (mem_Ex gs S i j).mp hj
      exact ⟨p, (mem_K gs S i p).mpr hp, (mem_Inp n gs p j).mpr hr⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hiK] at h1
  have h2 : ((K gs S i).biUnion (Inp n gs)).card ≤ 2 * (K gs S i).card := by
    calc _ ≤ ∑ p ∈ K gs S i, (Inp n gs p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ K gs S i, 2 := Finset.sum_le_sum fun p _ => Inp_card gs hg p
      _ = 2 * (K gs S i).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have h3 := Finset.card_pos.mpr ⟨i, hiK⟩
  omega

theorem frontier {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (S : Finset (Fin n)) (i : ℕ) (x y : Fin n → Bool) :
    ∀ p, InK gs S i p → val gs x p = true → val gs y p = false →
      ∃ e ∈ Ex gs S i, val gs x e = true ∧ val gs y e = false := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  intro hp hx hy
  obtain ⟨h1, h2⟩ := priv_range gs S p (InK_priv hp)
  obtain ⟨t, rfl⟩ : ∃ t, p = n + t := ⟨p - n, by omega⟩
  have ht : t < gs.length := by omega
  rw [val_gate gs x t ht] at hx
  rw [val_gate gs y t ht] at hy
  obtain ⟨j, hj, hxj, hyj⟩ := op_split _ (hg _ (List.getElem_mem ht)) _ _ _ hx hy
  have hjlt : j < n + t := by
    by_contra hc
    rw [val_big _ _ _ (by rw [List.length_take]; omega)] at hxj
    exact absurd hxj (by simp)
  rw [val_take gs x t j ht.le hjlt] at hxj
  rw [val_take gs y t j ht.le hjlt] at hyj
  have hr : RealIn n gs (n + t) j := ⟨t, ht, rfl, hj, hjlt⟩
  by_cases hpj : Priv gs S j
  · exact ih j hjlt (InK.step hp hr hpj) hxj hyj
  · exact ⟨j, (mem_Ex gs S i j).mpr ⟨hpj, _, hp, hr⟩, hxj, hyj⟩

theorem one_output {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (S : Finset (Fin n)) (k c o : ℕ)
    (hsub : Zs (n := n) gs o ⊆ S) (h2 : 2 ≤ (Zs (n := n) gs o).card)
    (hprom : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → val gs x o = false)
    (hck : c ≤ k) (hcA : c + 1 ≤ (Zs (n := n) gs o).card) :
    c ≤ (K gs S o).card := by
  classical
  have hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hg g h).1
  have hlen : ∀ g ∈ gs, g.inputs.length = 2 := fun g h => (hg g h).2
  have hpo : Priv gs S o := ⟨hsub, h2⟩
  have hex := ex_card gs hlen S o hpo
  let pick : ℕ → Finset (Fin n) := fun e =>
    if h : Zs (n := n) gs e ⊆ S then ∅ else {Classical.choose (Finset.not_subset.mp h)}
  have pick_card : ∀ e, (pick e).card ≤ 1 := by
    intro e
    simp only [pick]
    split_ifs <;> simp
  have pick_out : ∀ e, ∀ b ∈ pick e, b ∉ S := by
    intro e b hb
    simp only [pick] at hb
    split_ifs at hb with h
    · simp at hb
    · rw [Finset.mem_singleton] at hb
      subst hb
      exact (Classical.choose_spec (Finset.not_subset.mp h)).2
  have pick_in : ∀ e, ¬ Zs (n := n) gs e ⊆ S → ∃ b ∈ pick e, val gs (eof b) e = true := by
    intro e h
    refine ⟨Classical.choose (Finset.not_subset.mp h), by simp [pick, h], ?_⟩
    have := (Classical.choose_spec (Finset.not_subset.mp h)).1
    simpa [Zs] using this
  set B := (Ex gs S o).biUnion pick with hB
  have hBcard : B.card ≤ (Ex gs S o).card := by
    calc B.card ≤ ∑ e ∈ Ex gs S o, (pick e).card := Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ Ex gs S o, 1 := Finset.sum_le_sum fun e _ => pick_card e
      _ = (Ex gs S o).card := by simp
  let y : Fin n → Bool := fun a => decide (a ∈ B)
  have hy_bad : ∀ e ∈ Ex gs S o, ¬ Zs (n := n) gs e ⊆ S → val gs y e = true := by
    intro e he h
    obtain ⟨b, hb, hv⟩ := pick_in e h
    refine val_mono gs hop (eof b) y ?_ e hv
    intro a ha
    simp only [eof, decide_eq_true_eq] at ha
    subst ha
    simp only [y, decide_eq_true_eq, hB, Finset.mem_biUnion]
    exact ⟨e, he, hb⟩
  by_cases hyo : val gs y o = true
  · have hBS : ∀ q ∈ S, y q = false := by
      intro q hq
      simp only [y, decide_eq_false_iff_not, hB, Finset.mem_biUnion, not_exists, not_and]
      intro e _ hq'
      exact pick_out e q hq' hq
    have hfilt : (Finset.univ.filter (fun q => y q = true)) = B := by
      ext q
      simp [y]
    by_contra hlt
    have hk : (Finset.univ.filter (fun q => y q = true)).card ≤ k := by
      rw [hfilt]
      omega
    rw [hprom y hk hBS] at hyo
    exact absurd hyo (by simp)
  · have hyo' : val gs y o = false := by simpa using hyo
    have hmap : ∀ a ∈ Zs (n := n) gs o, ∃ e ∈ Ex gs S o,
        a ∈ Zs (n := n) gs e ∧ (Zs (n := n) gs e).card ≤ 1 := by
      intro a ha
      have hva : val gs (eof a) o = true := by simpa [Zs] using ha
      obtain ⟨e, he, hxe, hye⟩ := frontier gs hop S o (eof a) y o (InK.base hpo) hva hyo'
      have hsubS : Zs (n := n) gs e ⊆ S := by
        by_contra hc
        rw [hy_bad e he hc] at hye
        exact absurd hye (by simp)
      have hnp := ((mem_Ex gs S o e).mp he).1
      refine ⟨e, he, by simpa [Zs] using hxe, ?_⟩
      by_contra hc
      exact hnp ⟨hsubS, by omega⟩
    choose! f hf using hmap
    have hinj : Set.InjOn f (Zs (n := n) gs o : Set (Fin n)) := by
      intro a ha b hb hab
      obtain ⟨-, haz, hc⟩ := hf a ha
      obtain ⟨-, hbz, -⟩ := hf b hb
      rw [hab] at haz hc
      exact Finset.card_le_one.mp hc a haz b hbz
    have hmaps : ∀ a ∈ Zs (n := n) gs o, f a ∈ Ex gs S o := fun a ha => (hf a ha).1
    have := Finset.card_le_card_of_injOn f hmaps hinj
    omega

theorem wires_val (C : Circuit) {n : ℕ} (x : Fin n → Bool) (j : ℕ) :
    (C.wires (List.ofFn x)).getD j false = val C.gates x j := rfl

end PEqualNP.Outside.L_meta_782

open PEqualNP.Outside.L_meta_782 in
theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  classical
  intro n m k S C o c hS h2 hg hsub hprom hck hc1
  have hA : ∀ i, Zs (n := n) C.gates (o i) ⊆ S i := by
    intro i a ha
    exact hsub i a (Finset.mem_filter.mp ha).2
  have h2' : ∀ i, 2 ≤ (Zs (n := n) C.gates (o i)).card := fun i => h2 i
  have hc' : ∀ i, c i + 1 ≤ (Zs (n := n) C.gates (o i)).card := fun i => hc1 i
  have hprom' : ∀ i (x : Fin n → Bool), (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ S i, x q = false) → val C.gates x (o i) = false :=
    fun i x h1 h3 => hprom i x h1 h3
  let P : Fin m → Finset ℕ := fun i =>
    (Finset.Ico n (n + C.gates.length)).filter fun p => Priv C.gates (S i) p
  have hbound : ∀ i, c i ≤ (P i).card := by
    intro i
    have h := one_output C.gates hg (S i) k (c i) (o i) (hA i) (h2' i) (hprom' i) (hck i) (hc' i)
    refine h.trans (Finset.card_le_card ?_)
    intro p hp
    have hk := (mem_K C.gates (S i) (o i) p).mp hp
    have hpr := InK_priv hk
    have hr := priv_range C.gates (S i) p hpr
    simp only [P, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨hr, hpr⟩
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (P a) (P b) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro p hpa hpb
    simp only [P, Finset.mem_filter] at hpa hpb
    obtain ⟨-, hsa, h2a⟩ := hpa
    obtain ⟨-, hsb, -⟩ := hpb
    have hsub2 : Zs (n := n) C.gates p ⊆ S a ∩ S b := Finset.subset_inter hsa hsb
    have := Finset.card_le_card hsub2
    have := hS a b hab
    omega
  calc ∑ i, c i ≤ ∑ i, (P i).card := Finset.sum_le_sum fun i _ => hbound i
    _ = (Finset.univ.biUnion P).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + C.gates.length)).card := by
        apply Finset.card_le_card
        intro p hp
        obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hp
        simp only [P, Finset.mem_filter] at hi
        exact hi.1
    _ = C.size := by simp [PEqualNP.CircuitLowerBounds.Circuit.size]
