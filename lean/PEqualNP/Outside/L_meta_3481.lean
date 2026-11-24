import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3481
open PEqualNP.CircuitLowerBounds

theorem fold_ext (gs : List Gate) : ∀ (x : List Bool),
    ∃ t : List Bool, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
      = x ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro x; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro x
    obtain ⟨t, ht, hl⟩ := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => x.getD i false)] ++ t, ?_, ?_⟩
    · rw [List.foldl_cons, ht, List.append_assoc]
    · simp [hl]

theorem wires_ext (C : Circuit) (x : List Bool) :
    ∃ t : List Bool, C.wires x = x ++ t ∧ t.length = C.size := fold_ext C.gates x

end PEqualNP.Outside.L_meta_3481

theorem PEqualNP.Outside.L_meta_3481 : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 : Fin x1), x6 ≠ x7 → ¬x3.Adj x6 x7 → (2 : ℕ) ≤ (x3.neighborSet x6).ncard → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → ∃ (x12 : Fin x1), ¬(x3.Adj x6 x12 ↔ x3.Adj x7 x12)) → (∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → (2 : ℕ) ≤ (x3.neighborSet x8).ncard → ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x7 x12 ∧ x12 ≠ x8 ∧ x3.Adj x8 x13 ∧ x13 ≠ x7 ∧ (x12 = x13 ∨ ¬x3.Adj x12 x13)) → (∃ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → (2 : ℕ) ≤ (x3.neighborSet x9).ncard → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → x9 ∈ x8 ∨ x10 ∈ x8) ∧ x8.card = x2) → (∀ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x3.Adj x10 x11 → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → (2 : ℕ) ≤ (x3.neighborSet x11).ncard → x10 ∈ x9 ∨ x11 ∈ x9) → x2 ≤ x9.card) → PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 ∨ x1 + x4.size ≤ x4.output → (∀ (x12 x13 : Fin x1), x4.eval (List.ofFn fun (x14 : Fin x1) => Decidable.decide (x14 = x12 ∨ x14 = x13)) = Bool.true ↔ x3.Adj x12 x13) → x1 + x2 ≤ x4.size + (1 : ℕ) := by
  intro x1 x2 x3 x4 hnb _ _ _ hmin _ hout hiff
  rcases hout with h | h
  · exfalso
    have e := (hiff ⟨x4.output, h⟩ ⟨x4.output, h⟩).1
    apply x3.irrefl
    apply e
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    obtain ⟨t', ht', _⟩ := PEqualNP.Outside.L_meta_3481.wires_ext x4
      (List.ofFn fun (x14 : Fin x1) => Decidable.decide (x14 = ⟨x4.output, h⟩ ∨ x14 = ⟨x4.output, h⟩))
    rw [ht', List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h)]
    simp [h]
  · have hn : x1 = 0 := by
      by_contra hne
      obtain ⟨v, hv⟩ := hnb ⟨0, Nat.pos_of_ne_zero hne⟩
      have e := (hiff ⟨0, Nat.pos_of_ne_zero hne⟩ v).2 hv
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval at e
      obtain ⟨t', ht', htl'⟩ := PEqualNP.Outside.L_meta_3481.wires_ext x4
        (List.ofFn fun (x14 : Fin x1) => Decidable.decide (x14 = ⟨0, Nat.pos_of_ne_zero hne⟩ ∨ x14 = v))
      rw [ht', List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at e
      simp at e
    subst hn
    have := hmin ∅ (fun a => a.elim0)
    simp at this
    omega
