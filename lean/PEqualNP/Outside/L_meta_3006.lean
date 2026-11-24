import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3006
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem wires_snoc (gs : List Gate) (g : Gate) (o o' : ℕ) (y : List Bool) :
    (Circuit.mk (gs ++ [g]) o).wires y = (Circuit.mk gs o').wires y ++
      [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs o').wires y).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem tb_getD (L : List ℕ) (x7 i : ℕ) (hi : i < L.length) :
    (L.map fun x8 => x8.testBit x7).getD i false = (L[i]).testBit x7 := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem build (x1 : List ℕ) : ∀ x2 : List ℕ,
    (∀ x4 : Fin x2.length, ∃ x5 ∈ x1 ++ List.take (↑x4) x2, ∃ x6 ∈ x1 ++ List.take (↑x4) x2,
      x2.get x4 = x5 &&& x6 ∨ x2.get x4 = x5 ||| x6) →
    ∃ gs : List Gate, gs.length = x2.length ∧
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      ∀ x7 : ℕ, (Circuit.mk gs 0).wires (x1.map fun x8 => x8.testBit x7) =
        (x1 ++ x2).map fun x8 => x8.testBit x7 := by
  intro x2
  induction x2 using List.reverseRecOn with
  | nil =>
    intro _
    exact ⟨[], rfl, by simp, by intro x7; simp [Circuit.wires]⟩
  | append_singleton l v ih =>
    intro h
    have hl : ∀ x4 : Fin l.length, ∃ x5 ∈ x1 ++ List.take (↑x4) l, ∃ x6 ∈ x1 ++ List.take (↑x4) l,
        l.get x4 = x5 &&& x6 ∨ l.get x4 = x5 ||| x6 := by
      intro x4
      have hlt : x4.val < (l ++ [v]).length := by simp
      have h4 := h ⟨x4.val, hlt⟩
      have e1 : List.take x4.val (l ++ [v]) = List.take x4.val l :=
        List.take_append_of_le_length (by omega)
      have e2 : (l ++ [v]).get ⟨x4.val, hlt⟩ = l.get x4 := by
        simp [List.getElem_append_left x4.isLt]
      rw [e2] at h4
      simp only [e1] at h4
      exact h4
    obtain ⟨gs, hlen, hmon, hw⟩ := ih hl
    have hlt : l.length < (l ++ [v]).length := by simp
    have hv := h ⟨l.length, hlt⟩
    have e1 : List.take l.length (l ++ [v]) = l := by simp
    have e2 : (l ++ [v]).get ⟨l.length, hlt⟩ = v := by simp
    rw [e2] at hv
    simp only [e1] at hv
    obtain ⟨a, ha, b, hb, hab⟩ := hv
    obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
    obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hb
    rcases hab with hand | hor
    · refine ⟨gs ++ [⟨GateOp.and, [i, j]⟩], by simp [hlen], ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hmon g hg
        · simp only [List.mem_singleton] at hg
          subst hg
          simp
      · intro x7
        rw [wires_snoc gs _ 0 0, hw x7]
        simp only [List.map_cons, List.map_nil, tb_getD (x1 ++ l) x7 i hi, tb_getD (x1 ++ l) x7 j hj,
          hia, hjb]
        rw [← List.append_assoc, List.map_append, hand]
        simp [GateOp.eval, Nat.testBit_and]
    · refine ⟨gs ++ [⟨GateOp.or, [i, j]⟩], by simp [hlen], ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hmon g hg
        · simp only [List.mem_singleton] at hg
          subst hg
          simp
      · intro x7
        rw [wires_snoc gs _ 0 0, hw x7]
        simp only [List.map_cons, List.map_nil, tb_getD (x1 ++ l) x7 i hi, tb_getD (x1 ++ l) x7 j hj,
          hia, hjb]
        rw [← List.append_assoc, List.map_append, hor]
        simp [GateOp.eval, Nat.testBit_or]

end PEqualNP.Outside.L_meta_3006

theorem PEqualNP.Outside.L_meta_3006 : ∀ (x1 x2 : List ℕ) (x3 : ℕ), (∀ (x4 : Fin x2.length), ∃ x5 ∈ x1 ++ List.take (↑x4) x2, ∃ x6 ∈ x1 ++ List.take (↑x4) x2, x2.get x4 = x5 &&& x6 ∨ x2.get x4 = x5 ||| x6) → x3 ∈ x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x2.length ∧ ∀ (x7 : ℕ), x6.eval (List.map (fun (x8 : ℕ) => x8.testBit x7) x1) = x3.testBit x7 := by
  intro x1 x2 x3 h hmem
  obtain ⟨gs, hlen, hmon, hw⟩ := PEqualNP.Outside.L_meta_3006.build x1 x2 h
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hmem
  refine ⟨⟨gs, x1.length + j⟩, hmon, ?_, ?_⟩
  · show gs.length ≤ x2.length
    omega
  · intro x7
    show ((PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires
      (x1.map fun x8 => x8.testBit x7)).getD (x1.length + j) false = x3.testBit x7
    rw [hw x7, PEqualNP.Outside.L_meta_3006.tb_getD (x1 ++ x2) x7 (x1.length + j) (by simp; omega)]
    simp [hjx]
