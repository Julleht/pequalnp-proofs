import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3266
-- Frontier peeling: a set T of wires after a gate list is determined by a set S of wires
-- before it, with |S| <= |T| + (number of gates g with g.op.eval [false] = false).
-- step / snoc_getD_len copied from notes/tools/kit/lib.lean (L-meta-3081).
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem snoc_getD_len (l : List Bool) (v : Bool) (n : ℕ) (h : n = l.length) :
    (l ++ [v]).getD n false = v := by
  subst h
  simp [List.getD_eq_getElem?_getD]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem step_eq (w : List Bool) (g : Gate) (i : ℕ) (h : i = w.length) :
    (step w g).getD i false = g.op.eval (g.inputs.map fun j => w.getD j false) := by
  unfold step
  exact snoc_getD_len _ _ i h

theorem step_gt (w : List Bool) (g : Gate) (i : ℕ) (h : w.length < i) :
    (step w g).getD i false = false := by
  unfold step
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
  rfl

-- the wires a gate actually reads
def rd (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem gate_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ rd g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨op, ins⟩ := g
  cases op
  case not =>
    cases ins with
    | nil => rfl
    | cons a t => simp [GateOp.eval, h a (by simp [rd])]
  all_goals
    have e : ins.map f = ins.map f' := List.map_congr_left (fun i hi => h i (by simpa [rd] using hi))
    rw [e]

theorem rd_card (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (rd g).toFinset.card ≤ 1 + (if (!g.op.eval [false]) = true then 1 else 0) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hl
  rcases hop with h | h | h <;> subst h
  · have := List.toFinset_card_le ins
    simp [rd, GateOp.eval]; omega
  · have := List.toFinset_card_le ins
    simp [rd, GateOp.eval]; omega
  · have := List.toFinset_card_le (ins.take 1)
    have h2 : (ins.take 1).length ≤ 1 := by simp
    simp only [rd, GateOp.eval]
    simp
    omega

theorem len_fold (gs : List Gate) : ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    rw [ih]
    simp [step]
    omega

theorem peel (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ T : Finset ℕ, ∃ S : Finset ℕ,
      S.card ≤ T.card + gs.countP (fun g => !g.op.eval [false]) ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ T, (gs.foldl step x).getD i false = (gs.foldl step y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => intro T; exact ⟨T, by simp, fun x y _ _ h => h⟩
  | append_singleton l g ih =>
    intro T
    have hl : ∀ g' ∈ l, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (by simp [hg'])
    have hg := hgs g (by simp)
    obtain ⟨S, hS, hag⟩ := ih hl
      (if n + l.length ∈ T then T.erase (n + l.length) ∪ (rd g).toFinset else T)
    refine ⟨S, ?_, ?_⟩
    · have hc := rd_card g hg
      rw [List.countP_append, List.countP_singleton]
      generalize (if (!g.op.eval [false]) = true then 1 else 0) = e at hc ⊢
      have hT : (if n + l.length ∈ T then T.erase (n + l.length) ∪ (rd g).toFinset else T).card ≤
          T.card + e := by
        by_cases hm : n + l.length ∈ T
        · rw [if_pos hm]
          have h1 := Finset.card_union_le (T.erase (n + l.length)) (rd g).toFinset
          have h2 := Finset.card_erase_of_mem hm
          have h3 : 0 < T.card := Finset.card_pos.2 ⟨_, hm⟩
          omega
        · rw [if_neg hm]
          omega
      omega
    · intro x y hx hy h i hi
      have key := hag x y hx hy h
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlx : (l.foldl step x).length = n + l.length := by rw [len_fold, hx]
      have hly : (l.foldl step y).length = n + l.length := by rw [len_fold, hy]
      rcases Nat.lt_trichotomy i (n + l.length) with hlt | heq | hgt
      · have hi' : i ∈ (if n + l.length ∈ T then T.erase (n + l.length) ∪ (rd g).toFinset else T) := by
          by_cases hm : n + l.length ∈ T
          · rw [if_pos hm]
            exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨by omega, hi⟩)
          · rw [if_neg hm]
            exact hi
        rw [step_lt _ _ _ (by omega), step_lt _ _ _ (by omega)]
        exact key i hi'
      · rw [step_eq _ _ _ (by omega), step_eq _ _ _ (by omega)]
        apply gate_congr
        intro j hj
        apply key j
        rw [if_pos (heq ▸ hi)]
        exact Finset.mem_union_right _ (List.mem_toFinset.2 hj)
      · rw [step_gt _ _ _ (by omega), step_gt _ _ _ (by omega)]

theorem det (n : ℕ) (C : Circuit) (hC : FanInTwo C) :
    ∃ S : Finset ℕ, S.card ≤ C.gates.countP (fun g => !g.op.eval [false]) + 1 ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) → C.eval x = C.eval y := by
  obtain ⟨S, hS, hag⟩ := peel n C.gates hC {C.output}
  refine ⟨S, by simp at hS; omega, fun x y hx hy h => ?_⟩
  exact hag x y hx hy h C.output (Finset.mem_singleton_self _)

end PEqualNP.Outside.L_meta_3266

theorem PEqualNP.Outside.L_meta_3266 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : Finset ℕ), x4.card ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => !x5.op.eval [Bool.false]) x2.gates + (1 : ℕ) ∧ ∀ (x5 x6 : List Bool), x5.length = x1 → x6.length = x1 → (∀ x9 ∈ x4, x5.getD x9 Bool.false = x6.getD x9 Bool.false) → x2.eval x5 = x2.eval x6 := by
  intro x1 x2 hC
  exact PEqualNP.Outside.L_meta_3266.det x1 x2 hC
