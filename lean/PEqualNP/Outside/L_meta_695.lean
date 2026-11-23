import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_695

open PEqualNP.CircuitLowerBounds

def Zs (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p : Fin n =>
    (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true

def Priv (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  Zs n C w ⊆ S ∧ 2 ≤ (Zs n C w).card

def RealIn (n : ℕ) (C : Circuit) (p w : ℕ) : Prop :=
  ∃ t, ∃ ht : t < C.gates.length, p = n + t ∧ w ∈ (C.gates[t]).inputs ∧ w < p

inductive InK (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (i : ℕ) : ℕ → Prop
  | base : Priv n C S i → InK n C S i i
  | step {p w : ℕ} : InK n C S i p → RealIn n C p w → Priv n C S w → InK n C S i w

theorem InK_priv {n : ℕ} {C : Circuit} {S : Finset (Fin n)} {i p : ℕ}
    (h : InK n C S i p) : Priv n C S p := by
  cases h with
  | base h => exact h
  | step _ _ h => exact h

noncomputable def psi (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (Q : Finset ℕ) (w : ℕ) :
    Bool :=
  if n ≤ w ∧ w - n ∈ Q then
    match C.gates[w - n]? with
    | some g => g.op.eval (g.inputs.map fun u => if _h : u < w then psi n C S Q u else false)
    | none => false
  else decide (¬ Zs n C w ⊆ S)
termination_by w

end PEqualNP.Outside.L_meta_695

open PEqualNP.Outside.L_meta_695 in
theorem PEqualNP.Outside.L_meta_695 : ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → r < C.size → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)).card → ∃ (Q : Finset ℕ) (ψ : ℕ → Bool), r ∈ Q ∧ (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) ∧ (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) ∧ (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) ∧ (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) ∧ (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → (ψ w = true ↔ ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S)) := by
  classical
  intro n r S C _ hr hsub h2
  have hsz : C.size = C.gates.length := rfl
  let Q : Finset ℕ :=
    (Finset.range C.gates.length).filter fun j => InK n C S (n + r) (n + j)
  have memQ : ∀ j, j ∈ Q ↔ j < C.gates.length ∧ InK n C S (n + r) (n + j) := by
    intro j
    simp [Q]
  have hpr : Priv n C S (n + r) := ⟨hsub, h2⟩
  refine ⟨Q, psi n C S Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (memQ r).mpr ⟨by rw [← hsz]; exact hr, InK.base hpr⟩
  · intro j hj
    obtain ⟨hjl, hk⟩ := (memQ j).mp hj
    exact ⟨by rw [hsz]; exact hjl, (InK_priv hk).1, (InK_priv hk).2⟩
  · intro j hj hne
    obtain ⟨-, hk⟩ := (memQ j).mp hj
    generalize hw : n + j = w at hk
    cases hk with
    | base _ => exact absurd (by omega) hne
    | step hp hr' _ =>
      obtain ⟨t, ht, rfl, hin, hlt⟩ := hr'
      refine ⟨t, (memQ t).mpr ⟨ht, hp⟩, by omega, C.gates[t], List.getElem?_eq_getElem ht, ?_⟩
      exact hin
  · intro j hj j' hlt hex hs h2'
    obtain ⟨g, hgj, hin⟩ := hex
    obtain ⟨hjl, hk⟩ := (memQ j).mp hj
    have hgeq : C.gates[j] = g := by
      rw [List.getElem?_eq_getElem hjl] at hgj
      exact Option.some.inj hgj
    refine (memQ j').mpr ⟨by omega, InK.step hk ⟨j, hjl, rfl, ?_, by omega⟩ ⟨hs, h2'⟩⟩
    rw [hgeq]
    exact hin
  · intro j hj g hgj
    rw [psi, if_pos ⟨by omega, by simpa using hj⟩]
    simp only [Nat.add_sub_cancel_left, hgj, dite_eq_ite]
  · intro w hw
    rw [psi, if_neg]
    · exact decide_eq_true_iff
    · rintro ⟨h1, h3⟩
      exact hw (w - n) h3 (by omega)
