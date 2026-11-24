import Mathlib
import PEqualNP.Defs

-- Part 1 is copied from runs/w2295/L_meta_2295.lean (gate elimination framework).
namespace PEqualNP.Outside.L_meta_3102

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

-- ## Section 1: Self-contained circuit simplification, relabeling, and gate elimination

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


-- ## Part 2 (new for 3102): renaming without ReadsBack, agreement off two wires, counting two savings

def mapGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

-- old wire list W and new wire list N: every old wire except `bad` is the new wire ρ i
def Rel (ρ : ℕ → ℕ) (bad : ℕ) (W N : List Bool) : Prop :=
  N.length + 1 = W.length ∧ bad < W.length ∧ (∀ i, W.length ≤ i → ρ i = i - 1) ∧
  ∀ i, i < W.length → i ≠ bad → ρ i < N.length ∧ W.getD i false = N.getD (ρ i) false

theorem rel_all (ρ : ℕ → ℕ) (bad : ℕ) (W N : List Bool) (h : Rel ρ bad W N) :
    ∀ i, i ≠ bad → W.getD i false = N.getD (ρ i) false := by
  intro i hi
  by_cases hl : i < W.length
  · exact (h.2.2.2 i hl hi).2
  · have h1 := h.1
    rw [h.2.2.1 i (by omega), List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem rel_snoc (ρ : ℕ → ℕ) (bad : ℕ) (W N : List Bool) (h : Rel ρ bad W N) (v : Bool) :
    Rel ρ bad (W ++ [v]) (N ++ [v]) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simp; omega, by simp; omega, fun i hi => h3 i (by simp at hi; omega), fun i hi hib => ?_⟩
  simp only [List.length_append, List.length_singleton] at hi ⊢
  by_cases hl : i < W.length
  · obtain ⟨q1, q2⟩ := h4 i hl hib
    exact ⟨by omega, by rw [List.getD_append _ _ _ _ hl, List.getD_append _ _ _ _ q1]; exact q2⟩
  · have hiE : i = W.length := by omega
    have hρ : ρ i = N.length := by rw [h3 i (by omega)]; omega
    refine ⟨by omega, ?_⟩
    rw [hρ, hiE, getD_snoc_eq, getD_snoc_eq]

theorem phase (ρ : ℕ → ℕ) (bad : ℕ) : ∀ (gs : List Gate) (W N : List Bool), Rel ρ bad W N →
    (∀ g ∈ gs, bad ∉ g.inputs) → Rel ρ bad (wiresFrom gs W) (wiresFrom (gs.map (mapGate ρ)) N) := by
  intro gs
  induction gs with
  | nil => intro W N h _; exact h
  | cons g gs ih =>
    intro W N h hb
    have s1 : wiresFrom (g :: gs) W = wiresFrom gs (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: gs).map (mapGate ρ)) N = wiresFrom (gs.map (mapGate ρ))
        (N ++ [(mapGate ρ g).op.eval ((mapGate ρ g).inputs.map fun i => N.getD i false)]) := rfl
    have hval : (mapGate ρ g).op.eval ((mapGate ρ g).inputs.map fun i => N.getD i false) =
        g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact (rel_all ρ bad W N h a (fun e => hb g List.mem_cons_self (e ▸ ha))).symm
    rw [s1, s2, hval]
    exact ih _ _ (rel_snoc ρ bad W N h _) (fun g' hg' => hb g' (List.mem_cons_of_mem _ hg'))

-- two runs that differ only at wires k1 and k2 stay so, if every gate avoids both or is wire k2
theorem agree2 (k1 k2 : ℕ) : ∀ (gs : List Gate) (W W' : List Bool), W.length = W'.length →
    (∀ i, i ≠ k1 → i ≠ k2 → W.getD i false = W'.getD i false) →
    (∀ j (hj : j < gs.length), (k1 ∉ (gs[j]).inputs ∧ k2 ∉ (gs[j]).inputs) ∨ W.length + j = k2) →
    ∀ i, i ≠ k1 → i ≠ k2 → (wiresFrom gs W).getD i false = (wiresFrom gs W').getD i false := by
  intro gs
  induction gs with
  | nil => intro W W' _ h _; exact h
  | cons g gs ih =>
    intro W W' hl h hc
    have s1 : wiresFrom (g :: gs) W = wiresFrom gs (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) W' = wiresFrom gs (W' ++ [g.op.eval (g.inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2]
    apply ih _ _ (by simp [hl])
    · intro i hi1 hi2
      by_cases hil : i < W.length
      · rw [List.getD_append _ _ _ _ hil, List.getD_append _ _ _ _ (by omega)]; exact h i hi1 hi2
      · by_cases hie : i = W.length
        · rw [hie, getD_snoc_eq, getD_snoc_len _ _ _ _ hl.symm]
          rcases hc 0 (by simp) with ⟨n1, n2⟩ | he
          · congr 1
            apply List.map_congr_left
            intro a ha
            exact h a (fun e => n1 (by simpa [e] using ha)) (fun e => n2 (by simpa [e] using ha))
          · exact absurd (by simpa using hie.trans he) hi2
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · intro j hj
      have := hc (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rcases this with h' | h'
      · exact Or.inl h'
      · right; simp; omega

theorem take_succ' (l : List Gate) (X : ℕ) (h : X < l.length) : l.take (X + 1) = l.take X ++ [l[X]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some]

theorem len_take_mono (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (X Y : ℕ) (hXY : X ≤ Y) :
    (elim n (gs.take Y) acc).2.length ≤ (elim n (gs.take X) acc).2.length + (Y - X) := by
  have e : Y = X + (Y - X) := by omega
  rw [e, List.take_add, elim_append]
  have := elim_len n ((gs.drop X).take (Y - X)) (elim n (gs.take X) acc)
  have h2 : ((gs.drop X).take (Y - X)).length ≤ Y - X := by simp
  rw [Nat.add_sub_cancel_left]
  omega

def Saves (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (X : ℕ) : Prop :=
  ∃ hX : X < gs.length, ∃ k ∈ (gs[X]).inputs, ∃ c, (elim n (gs.take X) acc).1.getD k (Sum.inl false) = Sum.inl c

theorem saves_step (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (hok : ∀ g ∈ gs, NOk g) (X : ℕ)
    (h : Saves n gs acc X) : (elim n (gs.take (X + 1)) acc).2.length = (elim n (gs.take X) acc).2.length := by
  obtain ⟨hX, k, hk, c, hc⟩ := h
  rw [take_succ' gs X hX, elim_append]
  exact elimStep_none n _ (gs[X]) (hok _ (List.getElem_mem hX)) k hk c hc

theorem save_two (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (hok : ∀ g ∈ gs, NOk g) (p q : ℕ)
    (hpq : p < q) (hp : Saves n gs acc p) (hq : Saves n gs acc q) :
    (elim n gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  have hqL : q < gs.length := hq.1
  have a0 := len_take_mono n gs acc 0 p (by omega)
  have a1 := saves_step n gs acc hok p hp
  have a2 := len_take_mono n gs acc (p + 1) q (by omega)
  have a3 := saves_step n gs acc hok q hq
  have a4 := len_take_mono n gs acc (q + 1) gs.length (by omega)
  rw [List.take_length] at a4
  rw [List.take_zero] at a0
  have e0 : elim n [] acc = acc := rfl
  rw [e0] at a0
  omega

theorem simplify_inr (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : Sum.inl false ∈ ins) (j : ℕ)
    (hs : (simplify op m ins).2 = Sum.inr j) :
    op = GateOp.or ∧ (ins = [Sum.inl false, Sum.inr j] ∨ ins = [Sum.inr j, Sum.inl false]) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨(_ | _) | a, _ | ⟨(_ | _) | d, _ | ⟨e, l⟩⟩⟩ <;> simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨(_ | _) | a, _ | ⟨(_ | _) | d, _ | ⟨e, l⟩⟩⟩ <;> simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨(_ | _) | a, _ | ⟨d, l⟩⟩ <;> simp_all [simplify, simpNot]

theorem shape (l : List ℕ) (F : ℕ → Stat) (h6 : 6 ∈ l) (hF : F 6 = Sum.inl false) (j : ℕ)
    (h : l.map F = [Sum.inl false, Sum.inr j] ∨ l.map F = [Sum.inr j, Sum.inl false]) :
    ∃ n', n' ≠ 6 ∧ (l = [6, n'] ∨ l = [n', 6]) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h6
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hb6 : b ≠ 6 := fun e => by rw [e, hF] at hb; cases hb
    have ha6 : a = 6 := by omega
    exact ⟨b, hb6, Or.inl (by rw [ha6])⟩
  · have ha6 : a ≠ 6 := fun e => by rw [e, hF] at ha; cases ha
    have hb6 : b = 6 := by omega
    exact ⟨a, ha6, Or.inr (by rw [hb6])⟩

-- ## Part 3: the layout

def inp (b : Bool) (x : Fin 8 → Bool) : List Bool := [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]

def S0 : List Stat :=
  [Sum.inr 1, Sum.inr 0, Sum.inr 4, Sum.inr 7, Sum.inr 5, Sum.inr 2, Sum.inl false, Sum.inr 6, Sum.inr 3, Sum.inr 1]

def rho (i : ℕ) : ℕ := if i < 10 then [1, 0, 4, 7, 5, 2, 0, 6, 3, 8].getD i 0 else i - 1

theorem inv_S0 (y : Fin 8 → Bool) : Inv 8 (List.ofFn y) (inp false y) (S0, []) := by
  refine ⟨by simp [S0, inp], ?_⟩
  intro i
  by_cases hlt : i < 10
  · interval_cases i <;> simp [S0, inp, statValid, statVal, wiresFrom, List.ofFn_succ]
  · rw [List.getD_eq_default _ _ (by simp [S0]; omega), List.getD_eq_default _ _ (by simp [inp]; omega)]
    exact ⟨trivial, rfl⟩

theorem rel0 (b : Bool) (y : Fin 8 → Bool) : Rel rho 6 (inp b y) (List.ofFn y ++ [y 1 || b]) := by
  refine ⟨by simp [inp], by simp [inp], fun i hi => ?_, fun i hi h6 => ?_⟩
  · simp [inp] at hi; simp only [rho]; rw [if_neg (by omega)]
  · simp [inp] at hi
    interval_cases i <;> simp_all [rho, inp, List.ofFn_succ]

theorem agree0 (y : Fin 8 → Bool) (h1 : y 1 = true) (k2 : ℕ) :
    ∀ i, i ≠ 6 → i ≠ k2 → (inp false y).getD i false = (inp true y).getD i false := by
  intro i hi _
  by_cases hlt : i < 10
  · interval_cases i <;> simp_all [inp]
  · rw [List.getD_eq_default _ _ (by simp [inp]; omega), List.getD_eq_default _ _ (by simp [inp]; omega)]

theorem main (C : Circuit) (f0 f1 : (Fin 8 → Bool) → Bool) (hC : FanInTwo C) (hs : C.size ≤ 14)
    (hev : ∀ (b : Bool) (x : Fin 8 → Bool), C.eval (inp b x) = if b = true then f1 x else f0 x)
    (hx : ∃ x : Fin 8 → Bool, x 1 = true ∧ f0 x = false ∧ f1 x = true) :
    HasCircuitSize 8 f0 12 ∨ ∃ (C9 C10 : Circuit) (n : ℕ), FanInTwo C9 ∧ FanInTwo C10 ∧ C9.size + C10.size ≤ 13 ∧
      (∀ x : Fin 8 → Bool, C10.eval (C9.wires (List.ofFn x ++ [x 1 || false]) ++
          [(C9.wires (List.ofFn x ++ [x 1 || false])).getD n false]) = f0 x) ∧
      ∀ x : Fin 8 → Bool, C10.eval (C9.wires (List.ofFn x ++ [x 1 || true]) ++ [true]) = f1 x := by
  obtain ⟨x, hx1, hf0, hf1⟩ := hx
  have hok : ∀ g ∈ C.gates, Ok g := fun g hg => hC g hg
  set gs := C.gates.map normGate with hgsdef
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hokn : ∀ g ∈ gs, Ok g := fun g hg => (hnok g hg).1
  have hw : ∀ y : List Bool, wiresFrom gs y = C.wires y := fun y => wiresFrom_norm C.gates y
  have hL : gs.length ≤ 14 := by simpa [gs, Circuit.size] using hs
  have hE0 : ∀ (b : Bool) (y : Fin 8 → Bool),
      (wiresFrom gs (inp b y)).getD C.output false = if b = true then f1 y else f0 y := by
    intro b y; rw [hw]; exact hev b y
  set E := elim 8 gs (S0, []) with hEdef
  have hinvE : ∀ y : Fin 8 → Bool, Inv 8 (List.ofFn y) (wiresFrom gs (inp false y)) E :=
    fun y => inv_elim 8 _ (by simp) gs _ _ hokn (inv_S0 y)
  have hval : ∀ y : Fin 8 → Bool,
      statVal (wiresFrom E.2 (List.ofFn y)) (E.1.getD C.output (Sum.inl false)) = f0 y := by
    intro y; rw [((hinvE y).2 C.output).2, hE0]; simp
  have hE6 : ∀ X, (elim 8 (gs.take X) (S0, [])).1.getD 6 (Sum.inl false) = Sum.inl false :=
    fun X => by rw [elim_getD _ _ _ _ _ (by simp [S0])]; rfl
  cases hst : E.1.getD C.output (Sum.inl false) with
  | inl c =>
    left
    refine ⟨⟨[⟨GateOp.and, []⟩], if c then 8 else 9⟩, ?_, by simp [Circuit.size], ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      simp
    · intro y
      have := hval y
      rw [hst] at this
      simp only [statVal] at this
      rw [← this]
      cases c <;> simp [Circuit.eval, Circuit.wires, GateOp.eval]
  | inr j =>
  by_cases hsm : E.2.length ≤ 12
  · left
    refine ⟨⟨E.2, j⟩, fun g hg => elim_ok 8 gs (S0, []) (by simp) g hg, hsm, fun y => ?_⟩
    have := hval y
    rw [hst] at this
    exact this
  have htwo : ∀ p q, p < q → Saves 8 gs (S0, []) p → Saves 8 gs (S0, []) q → False := by
    intro p q hpq hp hq
    have : E.2.length + 2 ≤ ([] : List Gate).length + gs.length := save_two 8 gs (S0, []) hnok p q hpq hp hq
    simp only [List.length_nil] at this
    omega
  have ho6 : C.output ≠ 6 := by
    intro h
    rw [h, hEdef, elim_getD _ _ _ _ _ (by simp [S0])] at hst
    simp [S0] at hst
  by_cases hR : ∃ p, ∃ hp : p < gs.length, 6 ∈ (gs[p]).inputs
  · obtain ⟨p, hp, h6p⟩ := hR
    have hsave6 : ∀ q (hq : q < gs.length), 6 ∈ (gs[q]).inputs → Saves 8 gs (S0, []) q :=
      fun q hq h => ⟨hq, 6, h, false, hE6 q⟩
    have honly : ∀ q (hq : q < gs.length), q ≠ p → 6 ∉ (gs[q]).inputs := by
      intro q hq hqp h
      rcases Nat.lt_or_gt_of_ne hqp with hlt | hlt
      · exact htwo q p hlt (hsave6 q hq h) (hsave6 p hp h6p)
      · exact htwo p q hlt (hsave6 p hp h6p) (hsave6 q hq h)
    set A1 := elim 8 (gs.take p) (S0, []) with hA1
    set g := gs[p] with hg
    have hgmem : g ∈ gs := List.getElem_mem hp
    set s := (simplify g.op (8 + A1.2.length) (g.inputs.map fun i => A1.1.getD i (Sum.inl false))).2 with hsdef
    have hA1l : A1.1.length = 10 + p := by
      rw [hA1, elim_fst_len]; simp [S0]; omega
    have hsp : ∀ X, p < X → (elim 8 (gs.take X) (S0, [])).1.getD (10 + p) (Sum.inl false) = s := by
      intro X hX
      have e : X = (p + 1) + (X - (p + 1)) := by omega
      rw [e, List.take_add, elim_append, elim_getD _ _ _ _ _ (by rw [elim_fst_len]; simp [S0]; omega),
        take_succ' gs p hp, elim_append]
      show (A1.1 ++ [s]).getD (10 + p) (Sum.inl false) = s
      rw [getD_snoc_len _ _ _ _ hA1l]
    cases hs' : s with
    | inl c =>
      exfalso
      have hno : ∀ q (hq : q < gs.length), q ≠ p → 10 + p ∉ (gs[q]).inputs := by
        intro q hq hqp h
        rcases Nat.lt_or_gt_of_ne hqp with hlt | hlt
        · refine htwo q p hlt ⟨hq, 10 + p, h, false, ?_⟩ (hsave6 p hp h6p)
          apply List.getD_eq_default
          rw [elim_fst_len]; simp [S0]; omega
        · exact htwo p q hlt (hsave6 p hp h6p) ⟨hq, 10 + p, h, c, by rw [hsp q hlt, hs']⟩
      have ho2 : C.output ≠ 10 + p := by
        intro h
        have := hsp gs.length hp
        rw [List.take_length, ← hEdef, ← h, hst, hs'] at this
        cases this
      have hag := agree2 6 (10 + p) gs (inp false x) (inp true x) (by simp [inp]) (agree0 x hx1 (10 + p))
        (by
          intro q hq
          by_cases hqp : q = p
          · right; simp [inp, hqp]
          · exact Or.inl ⟨honly q hq hqp, hno q hq hqp⟩)
        C.output ho6 ho2
      rw [hE0, hE0] at hag
      simp [hf0, hf1] at hag
    | inr j' =>
      right
      obtain ⟨hop, hlen⟩ := (hnok g hgmem).1
      have hcl := simplify_inr g.op _ _ hop (by simpa using hlen) (fun h => by simpa using (hnok g hgmem).2 h)
        (List.mem_map.2 ⟨6, h6p, hE6 p⟩) j' (hsdef ▸ hs')
      obtain ⟨n', hn6, hin⟩ := shape g.inputs (fun i => A1.1.getD i (Sum.inl false)) h6p (hE6 p) j' hcl.2
      have hor := hcl.1
      set A := gs.take p with hAdef
      set B := gs.drop (p + 1) with hBdef
      have hsplit : gs = A ++ g :: B := by
        rw [hAdef, hBdef, hg]; simp
      have hA6 : ∀ g' ∈ A, 6 ∉ g'.inputs := by
        intro g' hg'
        obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.1 hg'
        have hqp : q < p := by simp [A] at hq; omega
        have := honly q (by omega) (by omega)
        simpa [A] using this
      have hB6 : ∀ g' ∈ B, 6 ∉ g'.inputs := by
        intro g' hg'
        obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.1 hg'
        have hq' : p + 1 + q < gs.length := by simp [B] at hq; omega
        have := honly (p + 1 + q) hq' (by omega)
        simpa [B] using this
      have hokA : ∀ g' ∈ A, Ok g' := fun g' h => hokn g' (List.mem_of_mem_take h)
      have hokB : ∀ g' ∈ B, Ok g' := fun g' h => hokn g' (List.mem_of_mem_drop h)
      refine ⟨⟨A.map (mapGate rho), 0⟩, ⟨B.map (mapGate rho), rho C.output⟩, rho n', ?_, ?_, ?_, ?_⟩
      · intro g' hg'
        obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hg'
        have := hokA h hh
        simpa [mapGate, Ok] using this
      · intro g' hg'
        obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hg'
        have := hokB h hh
        simpa [mapGate, Ok] using this
      · show (A.map _).length + (B.map _).length ≤ 13
        simp [A, B]; omega
      · -- the two evaluations
        have key : ∀ (b : Bool) (y : Fin 8 → Bool) (v : Bool),
            v = g.op.eval (g.inputs.map fun i => (wiresFrom A (inp b y)).getD i false) →
            (Circuit.mk (B.map (mapGate rho)) (rho C.output)).eval
              ((Circuit.mk (A.map (mapGate rho)) 0).wires (List.ofFn y ++ [y 1 || b]) ++ [v]) =
              if b = true then f1 y else f0 y := by
          intro b y v hv
          have r1 := phase rho 6 A _ _ (rel0 b y) hA6
          have r2 := phase rho 6 B _ _ (rel_snoc rho 6 _ _ r1 v) hB6
          have e1 : wiresFrom gs (inp b y) =
              wiresFrom B (wiresFrom A (inp b y) ++ [v]) := by
            rw [hsplit, wiresFrom_append, hv]; rfl
          rw [← hE0 b y, e1, rel_all rho 6 _ _ r2 C.output ho6]
          rfl
        have hW6 : ∀ b y, (wiresFrom A (inp b y)).getD 6 false = b := by
          intro b y
          rw [getD_wiresFrom _ _ _ (by simp [inp])]
          simp [inp]
        have hgv : ∀ b y, g.op.eval (g.inputs.map fun i => (wiresFrom A (inp b y)).getD i false) =
            (b || (wiresFrom A (inp b y)).getD n' false) := by
          intro b y
          rcases hin with e | e <;> rw [e, hor] <;>
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hW6,
              Bool.or_false] <;>
            generalize (wiresFrom A (inp b y)).getD n' false = t <;> cases b <;> cases t <;> rfl
        refine ⟨fun y => ?_, fun y => ?_⟩
        · have := key false y (((Circuit.mk (A.map (mapGate rho)) 0).wires
              (List.ofFn y ++ [y 1 || false])).getD (rho n') false) (by
            rw [hgv]
            have r1 := phase rho 6 A _ _ (rel0 false y) hA6
            rw [rel_all rho 6 _ _ r1 n' hn6, Bool.false_or]
            rfl)
          simpa using this
        · have := key true y true (by rw [hgv]; simp)
          simpa using this
  · exfalso
    push_neg at hR
    have hag := agree2 6 6 gs (inp false x) (inp true x) (by simp [inp]) (agree0 x hx1 6)
      (fun q hq => Or.inl ⟨hR q hq, hR q hq⟩) C.output ho6 ho6
    rw [hE0, hE0] at hag
    simp [hf0, hf1] at hag

end PEqualNP.Outside.L_meta_3102

theorem PEqualNP.Outside.L_meta_3102 : have x1 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x1 : Bool) (x2 : Fin (8 : ℕ) → Bool) => [x2 (1 : Fin (8 : ℕ)), x2 (0 : Fin (8 : ℕ)), x2 (4 : Fin (8 : ℕ)), x2 (7 : Fin (8 : ℕ)), x2 (5 : Fin (8 : ℕ)), x2 (2 : Fin (8 : ℕ)), x1, x2 (6 : Fin (8 : ℕ)), x2 (3 : Fin (8 : ℕ)), x2 (1 : Fin (8 : ℕ)) || x1]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : (Fin (8 : ℕ) → Bool) → Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (14 : ℕ) →       (∀ (x7 : Bool) (x8 : Fin (8 : ℕ) → Bool), x2.eval (x1 x7 x8) = if x7 = Bool.true then x4 x8 else x3 x8) →         (∃ (x8 : Fin (8 : ℕ) → Bool), x8 (1 : Fin (8 : ℕ)) = Bool.true ∧ x3 x8 = Bool.false ∧ x4 x8 = Bool.true) →           PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) x3 (12 : ℕ) ∨             ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : ℕ),               PEqualNP.MetaComplexity.FanInTwo x9 ∧                 PEqualNP.MetaComplexity.FanInTwo x10 ∧                   x9.size + x10.size ≤ (13 : ℕ) ∧                     have x12 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x12 : Bool) (x13 : Fin (8 : ℕ) → Bool) => x9.wires (List.ofFn x13 ++ [x13 (1 : Fin (8 : ℕ)) || x12]);                     (∀ (x13 : Fin (8 : ℕ) → Bool), x10.eval (x12 Bool.false x13 ++ [(x12 Bool.false x13).getD x11 Bool.false]) = x3 x13) ∧ ∀ (x13 : Fin (8 : ℕ) → Bool), x10.eval (x12 Bool.true x13 ++ [Bool.true]) = x4 x13 := by
  exact PEqualNP.Outside.L_meta_3102.main
