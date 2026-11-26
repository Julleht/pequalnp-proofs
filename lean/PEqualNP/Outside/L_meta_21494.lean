import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21494_aux

-- The circuit from the step's own sketch; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7]⟩], 8⟩

end PEqualNP.Outside.L_meta_21494_aux

theorem PEqualNP.Outside.L_meta_21494 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275423 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21494_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_21494_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
