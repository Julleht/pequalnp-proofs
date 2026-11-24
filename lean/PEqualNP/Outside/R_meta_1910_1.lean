import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1910_1
    (h1007 : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) 12)
    (hElim : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) →
      (∃ g ∈ C.gates.drop 1, ∃ p ∈ [4, 6], (g.inputs[0]? = some p ∨ g.op ≠ GateOp.not ∧ p ∈ g.inputs) ∧ (g.op = GateOp.and ∨ g.op = GateOp.not)) →
      ∃ s : ℕ, s + 3 ≤ C.size ∧ HasCircuitSize 8 (fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) s)
    (hCore : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) →
      (∀ p ∈ [4, 6], ∃! i : Fin (C.gates.drop 1).length,
        (C.gates.drop 1)[i].inputs[0]? = some p ∨
          (C.gates.drop 1)[i].op ≠ GateOp.not ∧ p ∈ (C.gates.drop 1)[i].inputs) →
      (∀ g ∈ C.gates.drop 1, ∀ p ∈ [4, 6], (g.inputs[0]? = some p ∨ g.op ≠ GateOp.not ∧ p ∈ g.inputs) → g.op ≠ GateOp.and ∧ g.op ≠ GateOp.not) →
      16 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) →       (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →         (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)],             ∃! x7 : Fin (List.drop (1 : ℕ) x1.gates).length,               have x8 : PEqualNP.CircuitLowerBounds.Gate := (List.drop (1 : ℕ) x1.gates).get x7;               x8.inputs[(0 : ℕ)]? = Option.some x5 ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x8.inputs) →           (16 : ℕ) ≤ x1.size := by
  intro C hfan hg1 hf huniq
  by_cases hP : ∃ g ∈ C.gates.drop 1, ∃ p ∈ [4, 6], (g.inputs[0]? = some p ∨ g.op ≠ GateOp.not ∧ p ∈ g.inputs) ∧ (g.op = GateOp.and ∨ g.op = GateOp.not)
  · obtain ⟨s, hs, D, hD, hDs, hDv⟩ := hElim C hfan hg1 hf hP
    by_contra hlt
    exact h1007 ⟨D, hD, by omega, hDv⟩
  · apply hCore C hfan hg1 hf
    · intro p hp
      obtain ⟨i, hi, hu⟩ := huniq p hp
      exact ⟨i, hi, fun j hj => hu j hj⟩
    · intro g hg p hp hr
      constructor
      · intro ha; exact hP ⟨g, hg, p, hp, hr, Or.inl ha⟩
      · intro hn; exact hP ⟨g, hg, p, hp, hr, Or.inr hn⟩

