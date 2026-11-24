import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3306
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

-- Swap the two inputs of an AND gate unless it already reads [p, q] with p in B and q in A.
def fix (A B : Finset ℕ) : Gate → Gate
  | ⟨GateOp.and, [u, v]⟩ => if u ∈ B ∧ v ∈ A then ⟨GateOp.and, [u, v]⟩ else ⟨GateOp.and, [v, u]⟩
  | g => g

theorem fix_cases (A B : Finset ℕ) (g : Gate) :
    fix A B g = g ∨ ∃ u v, g = ⟨GateOp.and, [u, v]⟩ ∧ fix A B g = ⟨GateOp.and, [v, u]⟩ := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨w, ins⟩⟩⟩ <;> simp only [fix] <;> try simp
  by_cases h : u ∈ B ∧ v ∈ A <;> tauto

theorem fix_op (A B : Finset ℕ) (g : Gate) : (fix A B g).op = g.op := by
  rcases fix_cases A B g with h | ⟨u, v, rfl, h⟩ <;> rw [h]

theorem fix_len (A B : Finset ℕ) (g : Gate) : (fix A B g).inputs.length = g.inputs.length := by
  rcases fix_cases A B g with h | ⟨u, v, rfl, h⟩ <;> rw [h]; rfl

theorem fix_mem (A B : Finset ℕ) (g : Gate) (i : ℕ) (hi : i ∈ (fix A B g).inputs) :
    i ∈ g.inputs := by
  rcases fix_cases A B g with h | ⟨u, v, rfl, h⟩
  · rw [h] at hi; exact hi
  · rw [h] at hi; simp at hi ⊢; tauto

theorem fix_eval (A B : Finset ℕ) (g : Gate) (f : ℕ → Bool) :
    (fix A B g).op.eval ((fix A B g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  rcases fix_cases A B g with h | ⟨u, v, rfl, h⟩
  · rw [h]
  · rw [h]; simp [GateOp.eval, Bool.and_comm]

theorem fix_or (A B : Finset ℕ) (g : Gate) (hg : g.op = GateOp.or) : fix A B g = g := by
  rcases fix_cases A B g with h | ⟨u, v, rfl, h⟩
  · exact h
  · simp at hg

theorem fix_and (A B : Finset ℕ) (u v : ℕ) (h : u ∈ A ∧ v ∈ B ∨ u ∈ B ∧ v ∈ A) :
    ∃ p q, (fix A B ⟨GateOp.and, [u, v]⟩).inputs = [p, q] ∧ p ∈ B ∧ q ∈ A := by
  simp only [fix]
  split_ifs with h2
  · exact ⟨u, v, rfl, h2.1, h2.2⟩
  · exact ⟨v, u, rfl, by tauto, by tauto⟩

theorem wires_fix (A B : Finset ℕ) (C : Circuit) (x : List Bool) :
    (Circuit.mk (C.gates.map (fix A B)) C.output).wires x = C.wires x := by
  simp only [Circuit.wires, List.foldl_map]
  congr 1
  funext w g
  rw [fix_eval]

theorem gateAt_fix (A B : Finset ℕ) (C : Circuit) (j : ℕ) :
    gateAt (Circuit.mk (C.gates.map (fix A B)) C.output) j = fix A B (gateAt C j) := by
  have hd : fix A B ⟨GateOp.or, []⟩ = ⟨GateOp.or, []⟩ := fix_or A B _ rfl
  simp only [gateAt]
  rw [← hd, List.getD_map, hd]

end PEqualNP.Outside.L_meta_3306

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_3306

theorem PEqualNP.Outside.L_meta_3306 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  intro x1 x2 x3 x4 hA hand
  obtain ⟨hao, hrb, hlen⟩ := hA
  refine ⟨Circuit.mk (x2.gates.map (fix x3 x4)) x2.output, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    rw [fix_op]; exact hao g0 hg0
  · intro j hj i hi
    rw [gateAt_fix] at hi
    simp only [List.length_map] at hj
    exact hrb j hj i (fix_mem _ _ _ _ hi)
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    rw [fix_len]; exact hlen g0 hg0
  · simp [Circuit.size]
  · funext x
    simp only [circuitFun, Circuit.eval, wires_fix]
  · intro j
    rw [gateAt_fix, fix_op]
  · intro j hj
    rw [gateAt_fix, fix_or _ _ _ hj]
  · intro j hj hop
    simp only [List.length_map] at hj
    rw [gateAt_fix, fix_op] at hop
    obtain ⟨u, v, huv, hm⟩ := hand j hj hop
    rw [gateAt_fix]
    have hg : gateAt x2 j = ⟨GateOp.and, [u, v]⟩ := by
      rw [← huv, ← hop]
    rw [hg]
    exact fix_and _ _ u v hm
