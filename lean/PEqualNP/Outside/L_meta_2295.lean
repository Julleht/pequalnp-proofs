import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2295

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

/-! ## Section 1: Self-contained circuit simplification, relabeling, and gate elimination -/

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp


def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩



/-! ## Section 2: fixing input 4 to false (the start state of the elimination) -/

/-- Stats for the 9 inputs with input 4 fixed to `false`; inputs 5..8 become restricted inputs 4..7. -/
def initS : List Stat :=
  [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7]

/-- The 9-input point that a restricted 8-input point `y` stands for. -/
def x9 (y : Fin 8 → Bool) : Fin 9 → Bool :=
  ![y 0, y 1, y 2, y 3, false, y 4, y 5, y 6, y 7]

theorem inv_initS (y : Fin 8 → Bool) :
    Inv 8 (List.ofFn y) (List.ofFn (x9 y)) (initS, []) := by
  refine ⟨by simp [initS], ?_⟩
  intro i
  by_cases hlt : i < 9
  · interval_cases i <;> simp [initS, statValid, statVal, wiresFrom, x9, List.ofFn_succ]
  · rw [List.getD_eq_default _ _ (by simp [initS]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

/-! ## Section 3: two inputs that differ at one unread wire -/

theorem agree_noread (k : ℕ) (gs : List Gate) (hk : ∀ g ∈ gs, k ∉ g.inputs) :
    ∀ w w' : List Bool, w.length = w'.length → (∀ i, i ≠ k → w.getD i false = w'.getD i false) →
      ∀ i, i ≠ k → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  induction gs with
  | nil => intro w w' _ h i hi; exact h i hi
  | cons g gs ih =>
    intro w w' hl h
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h a (fun e => hk g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w' = wiresFrom gs (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) := rfl
    rw [s1, s2]
    apply ih (fun g' hg' => hk g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hl])
    intro i hi
    rw [hv]
    by_cases hil : i < w.length
    · rw [List.getD_append _ _ _ _ hil, List.getD_append _ _ _ _ (by omega)]; exact h i hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

/-! ## Section 4: facts about the two functions -/

abbrev fP : (Fin 9 → Bool) → Bool := fun x4 : Fin 9 → Bool =>
  x4 0 && x4 1 || x4 1 && x4 2 || x4 2 && x4 3 || x4 3 && x4 4 || x4 4 && x4 0 || x4 0 && x4 5 ||
  x4 1 && x4 6 || x4 2 && x4 7 || x4 3 && x4 8 || x4 5 && x4 7 || x4 6 && x4 8 || x4 8 && x4 5

abbrev fQ : (Fin 8 → Bool) → Bool := fun x6 : Fin 8 → Bool =>
  x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 0 && x6 4 || x6 1 && x6 5 || x6 2 && x6 6 ||
  x6 3 && x6 7 || x6 4 && x6 6 || x6 5 && x6 7 || x6 7 && x6 4

theorem fP_x9 (y : Fin 8 → Bool) : fP (x9 y) = fQ y := by
  simp [fP, fQ, x9]

/-- A point given by the set of its true coordinates. -/
def pt9 (S : List ℕ) : Fin 9 → Bool := fun i => decide ((i : ℕ) ∈ S)

theorem getD_pt9 (S : List ℕ) (hS : ∀ s ∈ S, s < 9) (i : ℕ) :
    (List.ofFn (pt9 S)).getD i false = decide (i ∈ S) := by
  by_cases hi : i < 9
  · interval_cases i <;> simp [pt9, List.ofFn_succ]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    have : i ∉ S := fun h => hi (hS i h)
    simp [this]

/-! ## Section 5: the first gate is an AND reading input 4 -/

theorem first_and (g : Gate) (hok : Ok g)
    (h : ∀ x : Fin 9 → Bool, g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 && x 4)) :
    g.op = GateOp.and ∧ 4 ∈ g.inputs := by
  have h11 := h (pt9 [0, 4]); have h10 := h (pt9 [0]); have h01 := h (pt9 [4]); have h00 := h (pt9 [])
  simp only [getD_pt9 [0, 4] (by decide)] at h11
  simp only [getD_pt9 [0] (by decide)] at h10
  simp only [getD_pt9 [4] (by decide)] at h01
  simp only [getD_pt9 [] (by decide)] at h00
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, _⟩ := hok
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · refine ⟨rfl, ?_⟩
    simp [GateOp.eval, pt9] at h11 h10
    obtain ⟨i, hi, hi0⟩ := h10
    have := h11 i hi
    simp only at this hi0 ⊢
    rcases this with rfl | rfl
    · exact absurd rfl hi0
    · exact hi
  · simp [GateOp.eval, pt9] at h11 h10 h01
    obtain ⟨i, hi, hi04⟩ := h11
    rcases hi04 with rfl | rfl
    · exact (h10 _ hi rfl).elim
    · exact (h01 _ hi rfl).elim
  · cases ins <;> simp [GateOp.eval, pt9] at h00

/-! ## Section 6: the value of a gate's wire -/

theorem wire_at (gs : List Gate) (w : List Bool) (r : ℕ) (hr : r < gs.length)
    (hin : ∀ i ∈ (gs[r]).inputs, i < w.length + r) :
    (wiresFrom gs w).getD (w.length + r) false
      = (gs[r]).op.eval ((gs[r]).inputs.map fun i => (wiresFrom gs w).getD i false) := by
  have hsplit : gs = gs.take r ++ gs[r] :: gs.drop (r + 1) := by
    simp [List.take_append_drop]
  set pre := gs.take r
  set w1 := wiresFrom pre w with hw1
  have lw1 : w1.length = w.length + r := by
    rw [hw1, length_wiresFrom]; simp [pre, List.length_take]; omega
  have hfull : wiresFrom gs w
      = wiresFrom (gs.drop (r + 1)) (w1 ++ [(gs[r]).op.eval ((gs[r]).inputs.map fun i => w1.getD i false)]) := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  rw [hfull, getD_wiresFrom _ _ _ (by simp; omega), ← lw1, getD_snoc_eq]
  congr 1
  apply List.map_congr_left
  intro a ha
  have := hin a ha
  rw [getD_wiresFrom (gs.drop (r + 1)) _ a (by simp; omega), List.getD_append _ _ _ _ (by omega)]

/-! ## Section 7: shrinking a circuit at a gate whose value is known -/

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem eval_wiresFrom (C : Circuit) (x : List Bool) : C.eval x = (wiresFrom C.gates x).getD C.output false := rfl

/-- Re-run the elimination with nothing fixed, but replace gate `k` by the stat `s`, which must
carry the gate's value. The result is a circuit with one gate fewer computing the output wire. -/
theorem shrink (n : ℕ) (gs : List Gate) (o : ℕ) (hok : ∀ g ∈ gs, Ok g) (k : ℕ) (hk : k < gs.length)
    (s : Stat)
    (hs : ∀ y : Fin n → Bool,
      statValid (n + (elim n (gs.take k) (initId n, [])).2.length) s ∧
      statVal (wiresFrom (elim n (gs.take k) (initId n, [])).2 (List.ofFn y)) s
        = (gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) (List.ofFn y)).getD i false))
    (hnc : ∃ y y' : Fin n → Bool,
      (wiresFrom gs (List.ofFn y)).getD o false ≠ (wiresFrom gs (List.ofFn y')).getD o false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ gs.length ∧
      ∀ y : Fin n → Bool, D.eval (List.ofFn y) = (wiresFrom gs (List.ofFn y)).getD o false := by
  set pre := gs.take k
  set post := gs.drop (k + 1)
  have hsplit : gs = pre ++ gs[k] :: post := by simp [pre, post, List.take_append_drop]
  have hokpre : ∀ g ∈ pre, Ok g := fun g hg => hok g (List.mem_of_mem_take hg)
  have hokpost : ∀ g ∈ post, Ok g := fun g hg => hok g (List.mem_of_mem_drop hg)
  set A1 := elim n pre (initId n, [])
  set A2 : List Stat × List Gate := (A1.1 ++ [s], A1.2)
  set A3 := elim n post A2
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom gs (List.ofFn y)) A3 := by
    intro y
    have h1 : Inv n (List.ofFn y) (wiresFrom pre (List.ofFn y)) A1 :=
      inv_elim n _ (by simp) pre _ _ hokpre (inv_initId n y)
    set v := (gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom pre (List.ofFn y)).getD i false)
    have h2 : Inv n (List.ofFn y) (wiresFrom pre (List.ofFn y) ++ [v]) A2 := by
      obtain ⟨hl, hi⟩ := h1
      refine ⟨by simp [A2, hl], ?_⟩
      intro i
      by_cases hil : i = A1.1.length
      · subst hil
        show statValid _ ((A1.1 ++ [s]).getD A1.1.length _) ∧ statVal _ ((A1.1 ++ [s]).getD A1.1.length _) = _
        rw [getD_snoc_eq, hl, getD_snoc_eq]
        exact hs y
      · show statValid _ ((A1.1 ++ [s]).getD i _) ∧ statVal _ ((A1.1 ++ [s]).getD i _) = _
        rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by rw [← hl]; exact hil)]
        exact hi i
    have h3 := inv_elim n _ (by simp) post _ _ hokpost h2
    have he : wiresFrom gs (List.ofFn y) = wiresFrom post (wiresFrom pre (List.ofFn y) ++ [v]) := by
      conv_lhs => rw [hsplit]
      rw [wiresFrom_append]; rfl
    rw [he]; exact h3
  have hlen : A3.2.length + 1 ≤ gs.length := by
    have l1 : A1.2.length ≤ pre.length := by
      have := elim_len n pre (initId n, []); simpa using this
    have l3 : A3.2.length ≤ A1.2.length + post.length := elim_len n post A2
    have lg : gs.length = pre.length + 1 + post.length := by
      conv_lhs => rw [hsplit]
      simp; omega
    omega
  have hok3 : ∀ g ∈ A3.2, Ok g := by
    apply elim_ok n post A2
    exact elim_ok n pre (initId n, []) (by simp)
  cases hst : A3.1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    have e1 := ((hinv y).2 o).2
    have e2 := ((hinv y').2 o).2
    rw [hst] at e1 e2
    exact hne (e1.symm.trans e2)
  | inr j =>
    refine ⟨⟨A3.2, j⟩, fun g hg => hok3 g hg, hlen, ?_⟩
    intro y
    have e1 := ((hinv y).2 o).2
    rw [hst] at e1
    exact e1

/-! ## Section 8: three saved gates -/

theorem save_one (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (hok : ∀ g ∈ gs, NOk g)
    (X : ℕ) (hX : X < gs.length) (k : ℕ) (hk : k ∈ (gs[X]).inputs) (hkl : k < acc.1.length + X)
    (hc : ∃ c, (elim n (gs.take X) acc).1.getD k (Sum.inl false) = Sum.inl c) :
    (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  have hsplit : gs = gs.take X ++ gs.drop X := (List.take_append_drop X gs).symm
  have e : elim n gs acc = elim n (gs.drop X) (elim n (gs.take X) acc) := by
    conv_lhs => rw [hsplit]
    exact elim_append n _ _ acc
  rw [e]
  have l1 := elim_len n (gs.take X) acc
  have l2 := elim_len_lt n k (gs.drop X) (elim n (gs.take X) acc)
    (fun g hg => hok g (List.mem_of_mem_drop hg))
    (by rw [elim_fst_len]; simp [List.length_take]; omega) hc
    ⟨gs[X], by
      rw [List.mem_iff_getElem]
      exact ⟨0, by simp; omega, by simp⟩, hk⟩
  have lt : (gs.take X).length + (gs.drop X).length = gs.length := by simp; omega
  omega

theorem save_three (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (hok : ∀ g ∈ gs, NOk g)
    (p q : ℕ) (h0 : 0 < p) (hpq : p < q) (hq : q < gs.length)
    (k0 kp kq : ℕ) (hk0 : k0 ∈ (gs[0]'(by omega)).inputs) (hkp : kp ∈ (gs[p]'(by omega)).inputs)
    (hkq : kq ∈ (gs[q]).inputs)
    (hl0 : k0 < acc.1.length) (hlp : kp < acc.1.length + p) (hlq : kq < acc.1.length + q)
    (hc0 : ∃ c, acc.1.getD k0 (Sum.inl false) = Sum.inl c)
    (hcp : ∃ c, (elim n (gs.take p) acc).1.getD kp (Sum.inl false) = Sum.inl c)
    (hcq : ∃ c, (elim n (gs.take q) acc).1.getD kq (Sum.inl false) = Sum.inl c) :
    (elim n gs acc).2.length + 3 ≤ acc.2.length + gs.length := by
  set A := gs.take p
  set B := (gs.drop p).take (q - p)
  set Cc := gs.drop q
  have hAB : A ++ B = gs.take q := by
    simp only [A, B]
    rw [← List.take_add, Nat.add_sub_cancel' (by omega)]
  have hsplit : gs = A ++ B ++ Cc := by rw [hAB]; simp [Cc]
  have hokA : ∀ g ∈ A, NOk g := fun g hg => hok g (List.mem_of_mem_take hg)
  have hokB : ∀ g ∈ B, NOk g := fun g hg => hok g (List.mem_of_mem_drop (List.mem_of_mem_take hg))
  have hokC : ∀ g ∈ Cc, NOk g := fun g hg => hok g (List.mem_of_mem_drop hg)
  have lA : A.length = p := by simp [A]; omega
  have lB : B.length = q - p := by simp [B]; omega
  have lC : Cc.length = gs.length - q := by simp [Cc]
  have e : elim n gs acc = elim n Cc (elim n B (elim n A acc)) := by
    conv_lhs => rw [hsplit]
    rw [elim_append, elim_append]
  have eAB : elim n B (elim n A acc) = elim n (gs.take q) acc := by
    rw [← hAB, elim_append]
  have s1 := save_one n A acc hokA 0 (by omega) k0 (by simpa [A] using hk0) (by omega)
    (by rw [List.take_zero]; exact hc0)
  have s2 := save_one n B (elim n A acc) hokB 0 (by omega) kp
    (by simpa [B, List.getElem_take, List.getElem_drop] using hkp)
    (by rw [elim_fst_len]; omega) (by rw [List.take_zero]; exact hcp)
  have s3 := save_one n Cc (elim n B (elim n A acc)) hokC 0 (by omega) kq
    (by simpa [Cc, List.getElem_drop] using hkq)
    (by rw [elim_fst_len, elim_fst_len]; omega) (by rw [List.take_zero, eAB]; exact hcq)
  rw [e]
  omega

theorem pair_of_two (l : List ℕ) (a b : ℕ) (hl : l.length ≤ 2) (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    l = [a, b] ∨ l = [b, a] := by
  rcases l with _ | ⟨u, _ | ⟨v, _ | ⟨w, t⟩⟩⟩
  · simp at ha
  · simp at ha hb; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  · simp at hl

theorem fP_pt34 : fP (pt9 [3, 4]) = true := by decide
theorem fP_pt3 : fP (pt9 [3]) = false := by decide
theorem fP_pt4 : fP (pt9 [4]) = false := by decide
theorem fP_pt01 : fP (pt9 [0, 1]) = true := by decide
theorem fP_pt0 : fP (pt9 []) = false := by decide

theorem fQ_nc : fQ (fun _ => false) = false ∧ fQ (fun i => decide ((i : ℕ) < 2)) = true := by decide

theorem main_2295 (C : Circuit) (hmin : IsMinimalCircuit 9 C)
    (hg1 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 4))
    (hf : circuitFun 9 C = fP) :
    ∃ s : ℕ, s + 3 ≤ C.size ∧ HasCircuitSize 8 fQ s := by
  have hok : ∀ g ∈ C.gates, Ok g := fun g hg => hmin.1 g hg
  set gs := C.gates.map normGate with hgsdef
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hokn : ∀ g ∈ gs, Ok g := fun g hg => (hnok g hg).1
  have hw : ∀ x : List Bool, wiresFrom gs x = C.wires x := fun x => wiresFrom_norm C.gates x
  have hsize : gs.length = C.size := by simp [gs, Circuit.size]
  have hfx : ∀ x : Fin 9 → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = fP x := by
    intro x; rw [hw]; exact congrFun hf x
  -- the gates are not empty
  obtain ⟨g0, rest, hgs⟩ : ∃ g0 rest, gs = g0 :: rest := by
    cases h : gs with
    | nil =>
      exfalso
      have := hg1 (pt9 [0, 4])
      rw [← hw, h] at this
      simp [wiresFrom, pt9] at this
    | cons g0 rest => exact ⟨g0, rest, rfl⟩
  have hw9 : ∀ x : List Bool, x.length = 9 →
      wiresFrom gs x = wiresFrom rest (x ++ [g0.op.eval (g0.inputs.map fun i => x.getD i false)]) := by
    intro x _; rw [hgs]; rfl
  have hv9 : ∀ x : Fin 9 → Bool,
      g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 && x 4) := by
    intro x
    have := hg1 x
    rw [← hw, hw9 _ (by simp), getD_wiresFrom _ _ _ (by simp)] at this
    simpa using this
  obtain ⟨hand, h4⟩ := first_and g0 (hokn g0 (by simp [hgs])) hv9
  have hmem : ∀ g ∈ rest, g ∈ gs := fun g hg => by rw [hgs]; exact List.mem_cons_of_mem _ hg
  have hnc : ∃ y y' : Fin 9 → Bool,
      (wiresFrom gs (List.ofFn y)).getD C.output false ≠ (wiresFrom gs (List.ofFn y')).getD C.output false :=
    ⟨pt9 [0, 1], pt9 [], by rw [hfx, hfx, fP_pt01, fP_pt0]; decide⟩
  -- a circuit for the same function with fewer gates is impossible
  have hsmall : ∀ D : Circuit, FanInTwo D → D.size + 1 ≤ gs.length →
      (∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = (wiresFrom gs (List.ofFn y)).getD C.output false) → False := by
    intro D hD hDs hDv
    have := hmin.2 D hD (by funext y; rw [show circuitFun 9 D y = D.eval (List.ofFn y) from rfl, hDv, hfx, ← hf])
    omega
  -- (A) some later gate reads wire 9
  have hA : ∃ a, ∃ ha : a < rest.length, 9 ∈ (rest[a]).inputs := by
    by_contra hnone
    have hnr : ∀ g ∈ rest, 9 ∉ g.inputs := by
      intro g hg h9
      obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 hg
      exact hnone ⟨a, ha, h9⟩
    by_cases ho : C.output = 9
    · have := hfx (pt9 [3, 4])
      rw [hw9 _ (by simp), ho, getD_wiresFrom _ _ _ (by simp), hv9] at this
      rw [fP_pt34] at this
      simp [pt9] at this
    · set gs' : List Gate := ⟨GateOp.and, []⟩ :: rest
      have hval : ∀ y : Fin 9 → Bool, (wiresFrom gs' (List.ofFn y)).getD C.output false
          = (wiresFrom gs (List.ofFn y)).getD C.output false := by
        intro y
        rw [hw9 _ (by simp)]
        show (wiresFrom rest (List.ofFn y ++ [true])).getD C.output false = _
        apply agree_noread 9 rest hnr _ _ (by simp) _ _ ho
        intro i hi
        by_cases hil : i < 9
        · rw [List.getD_append _ _ _ _ (by simpa using hil), List.getD_append _ _ _ _ (by simpa using hil)]
        · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
          simp only [List.length_ofFn]
          rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have hok' : ∀ g ∈ gs', Ok g := by
        intro g hg
        rcases List.mem_cons.1 hg with rfl | h
        · exact ⟨Or.inl rfl, by simp⟩
        · exact hokn g (hmem g h)
      obtain ⟨D, hD, hDs, hDv⟩ := shrink 9 gs' C.output hok' 0 (by simp [gs']) (Sum.inl true)
        (fun y => ⟨trivial, by simp [gs', statVal, GateOp.eval]⟩)
        (by obtain ⟨y, y', h⟩ := hnc; exact ⟨y, y', by rw [hval, hval]; exact h⟩)
      exact hsmall D hD (by simpa [gs', hgs] using hDs) (fun y => by rw [hDv, hval])
  -- (B) some later gate reads input 4
  have hB : ∃ b, ∃ hb : b < rest.length, 4 ∈ (rest[b]).inputs := by
    by_contra hnone
    have hnr : ∀ g ∈ rest, 4 ∉ g.inputs := by
      intro g hg h
      obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.1 hg
      exact hnone ⟨b, hb, h⟩
    by_cases ho : C.output = 4
    · have := hfx (pt9 [4])
      rw [ho, getD_wiresFrom _ _ _ (by simp), fP_pt4] at this
      simp [pt9] at this
    · have e1 := hfx (pt9 [3, 4])
      have e2 := hfx (pt9 [3])
      rw [hw9 _ (by simp), hv9] at e1 e2
      have heq : (wiresFrom rest (List.ofFn (pt9 [3, 4]) ++ [(pt9 [3, 4] 0 && pt9 [3, 4] 4)])).getD C.output false
          = (wiresFrom rest (List.ofFn (pt9 [3]) ++ [(pt9 [3] 0 && pt9 [3] 4)])).getD C.output false := by
        apply agree_noread 4 rest hnr _ _ (by simp) _ _ ho
        intro i hi
        by_cases hil : i < 9
        · rw [List.getD_append _ _ _ _ (by simpa using hil), List.getD_append _ _ _ _ (by simpa using hil),
            getD_pt9 _ (by decide), getD_pt9 _ (by decide)]
          simp; omega
        · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
          simp only [List.length_ofFn]
          by_cases h9 : i = 9
          · subst h9; simp [pt9]
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      rw [e1, e2, fP_pt34, fP_pt3] at heq
      exact absurd heq (by decide)
  -- (C) no later gate reads both input 4 and wire 9
  have hC : ∀ r, ∀ hr : r < rest.length, ¬ (4 ∈ (rest[r]).inputs ∧ 9 ∈ (rest[r]).inputs) := by
    intro r hr ⟨h4r, h9r⟩
    set gr := rest[r]
    have hgr : gr ∈ gs := hmem gr (List.getElem_mem hr)
    obtain ⟨⟨hop, hlen⟩, hnot⟩ := hnok gr hgr
    have hpair := pair_of_two gr.inputs 4 9 hlen h4r h9r (by decide)
    have hk : r + 1 < gs.length := by rw [hgs]; simp; omega
    have hgsr : gs[r + 1] = gr := by simp [hgs, gr]
    have htake : gs.take (r + 1) = g0 :: rest.take r := by rw [hgs]; simp
    have hpre : ∀ y : Fin 9 → Bool, ∀ i, i ≤ 9 → (wiresFrom (gs.take (r + 1)) (List.ofFn y)).getD i false
        = (List.ofFn y ++ [(y 0 && y 4)]).getD i false := by
      intro y i hi
      rw [htake]
      show (wiresFrom (rest.take r) (List.ofFn y ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false)])).getD i false = _
      rw [getD_wiresFrom _ _ _ (by simp; omega), hv9]
    have h4v : ∀ y : Fin 9 → Bool, (wiresFrom (gs.take (r + 1)) (List.ofFn y)).getD 4 false = y 4 := by
      intro y; rw [hpre y 4 (by omega), List.getD_append _ _ _ _ (by simp)]; simp
    have h9v : ∀ y : Fin 9 → Bool, (wiresFrom (gs.take (r + 1)) (List.ofFn y)).getD 9 false = (y 0 && y 4) := by
      intro y; rw [hpre y 9 (by omega)]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have hcopy : ∀ j, (∀ y : Fin 9 → Bool,
        gr.op.eval (gr.inputs.map fun i => (wiresFrom (gs.take (r + 1)) (List.ofFn y)).getD i false)
          = (wiresFrom (gs.take (r + 1)) (List.ofFn y)).getD j false) → j < 9 + (r + 1) → False := by
      intro j hj hjl
      have hokt : ∀ g ∈ gs.take (r + 1), Ok g := fun g hg => hokn g (List.mem_of_mem_take hg)
      obtain ⟨D, hD, hDs, hDv⟩ := shrink 9 gs C.output hokn (r + 1) hk
        ((elim 9 (gs.take (r + 1)) (initId 9, [])).1.getD j (Sum.inl false))
        (fun y => by
          have Iv := inv_elim 9 (List.ofFn y) (by simp) (gs.take (r + 1)) (List.ofFn y) (initId 9, []) hokt
            (inv_initId 9 y)
          refine ⟨(Iv.2 j).1, ?_⟩
          rw [(Iv.2 j).2]
          simp only [hgsr]
          exact (hj y).symm)
        hnc
      exact hsmall D hD hDs hDv
    rcases hop with hop | hop | hop
    · apply hcopy 9 _ (by omega)
      intro y
      rcases hpair with h | h <;> rw [h, hop] <;>
        simp only [GateOp.eval, List.map_cons, List.map_nil, h4v, h9v, List.all_cons, List.all_nil,
          List.any_cons, List.any_nil, id_eq] <;>
        cases y 0 <;> cases y 4 <;> rfl
    · apply hcopy 4 _ (by omega)
      intro y
      rcases hpair with h | h <;> rw [h, hop] <;>
        simp only [GateOp.eval, List.map_cons, List.map_nil, h4v, h9v, List.all_cons, List.all_nil,
          List.any_cons, List.any_nil, id_eq] <;>
        cases y 0 <;> cases y 4 <;> rfl
    · have := hnot hop
      rcases hpair with h | h <;> rw [h] at this <;> simp at this
  -- two distinct later gates read the constants 4 and 9
  obtain ⟨a, ha, h9a⟩ := hA
  obtain ⟨b, hb, h4b⟩ := hB
  have hab : a ≠ b := by rintro rfl; exact hC a ha ⟨h4b, h9a⟩
  set E := elim 8 gs (initS, [])
  have hinvE : ∀ y : Fin 8 → Bool, Inv 8 (List.ofFn y) (wiresFrom gs (List.ofFn (x9 y))) E :=
    fun y => inv_elim 8 _ (by simp) gs _ _ hokn (inv_initS y)
  have hc4 : ∀ X, ∃ c, (elim 8 (gs.take X) (initS, [])).1.getD 4 (Sum.inl false) = Sum.inl c :=
    fun X => ⟨false, by rw [elim_getD _ _ _ _ _ (by simp [initS])]; rfl⟩
  have hc9 : ∀ X, 1 ≤ X → ∃ c, (elim 8 (gs.take X) (initS, [])).1.getD 9 (Sum.inl false) = Sum.inl c := by
    intro X hX
    have ht : gs.take X = g0 :: rest.take (X - 1) := by
      rw [hgs]; obtain ⟨X', rfl⟩ : ∃ X', X = X' + 1 := ⟨X - 1, by omega⟩; simp
    rw [ht, elim_cons, elim_getD _ _ _ _ _ (by simp [elimStep, initS])]
    have := elimStep_const 8 (initS, []) g0 (hnok g0 (by simp [hgs])) 4 h4 (by simp [initS, fixBit, hand])
    simpa [initS] using this
  have hg0 : gs[0]'(by rw [hgs]; simp) = g0 := by simp [hgs]
  have hga : gs[a + 1]'(by rw [hgs]; simp; omega) = rest[a] := by simp [hgs]
  have hgb : gs[b + 1]'(by rw [hgs]; simp; omega) = rest[b] := by simp [hgs]
  have hglen : gs.length = rest.length + 1 := by rw [hgs]; simp
  have hcount : E.2.length + 3 ≤ gs.length := by
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · have := save_three 8 gs (initS, []) hnok (a + 1) (b + 1) (by omega) (by omega) (by omega)
        4 9 4 (by rw [hg0]; exact h4) (by rw [hga]; exact h9a) (by rw [hgb]; exact h4b)
        (by simp only [initS, List.length_cons, List.length_nil]; omega)
        (by simp only [initS, List.length_cons, List.length_nil]; omega)
        (by simp only [initS, List.length_cons, List.length_nil]; omega)
        ⟨false, rfl⟩ (hc9 (a + 1) (by omega)) (hc4 (b + 1))
      simpa using this
    · have := save_three 8 gs (initS, []) hnok (b + 1) (a + 1) (by omega) (by omega) (by omega)
        4 4 9 (by rw [hg0]; exact h4) (by rw [hgb]; exact h4b) (by rw [hga]; exact h9a)
        (by simp only [initS, List.length_cons, List.length_nil]; omega)
        (by simp only [initS, List.length_cons, List.length_nil]; omega)
        (by simp only [initS, List.length_cons, List.length_nil]; omega)
        ⟨false, rfl⟩ (hc4 (b + 1)) (hc9 (a + 1) (by omega))
      simpa using this
  have hval : ∀ y : Fin 8 → Bool,
      statVal (wiresFrom E.2 (List.ofFn y)) (E.1.getD C.output (Sum.inl false)) = fQ y := by
    intro y
    rw [((hinvE y).2 C.output).2, hfx, fP_x9]
  cases hst : E.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    have e1 := hval (fun _ => false)
    have e2 := hval (fun i => decide ((i : ℕ) < 2))
    rw [hst] at e1 e2
    have := fQ_nc
    simp only [statVal] at e1 e2
    rw [← e1, ← e2] at this
    exact absurd (this.1.symm.trans this.2) (by decide)
  | inr j =>
    refine ⟨E.2.length, by omega, ⟨E.2, j⟩, fun g hg => elim_ok 8 gs (initS, []) (by simp) g hg, le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_2295

open PEqualNP.Outside.L_meta_2295 in
theorem PEqualNP.Outside.L_meta_2295 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∃ (x5 : ℕ), x5 + (3 : ℕ) ≤ x1.size ∧ PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x6 : Fin (8 : ℕ) → Bool) => x6 (0 : Fin (8 : ℕ)) && x6 (1 : Fin (8 : ℕ)) || x6 (1 : Fin (8 : ℕ)) && x6 (2 : Fin (8 : ℕ)) || x6 (2 : Fin (8 : ℕ)) && x6 (3 : Fin (8 : ℕ)) || x6 (0 : Fin (8 : ℕ)) && x6 (4 : Fin (8 : ℕ)) || x6 (1 : Fin (8 : ℕ)) && x6 (5 : Fin (8 : ℕ)) || x6 (2 : Fin (8 : ℕ)) && x6 (6 : Fin (8 : ℕ)) || x6 (3 : Fin (8 : ℕ)) && x6 (7 : Fin (8 : ℕ)) || x6 (4 : Fin (8 : ℕ)) && x6 (6 : Fin (8 : ℕ)) || x6 (5 : Fin (8 : ℕ)) && x6 (7 : Fin (8 : ℕ)) || x6 (7 : Fin (8 : ℕ)) && x6 (4 : Fin (8 : ℕ))) x5 := by
  intro x1 hmin hg1 hf
  exact main_2295 x1 hmin hg1 hf

