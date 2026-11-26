import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20372

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- An AND/OR circuit of 28 fan-in-two gates; wires 0-7 the left vertices, 8-15 the right. -/
def circ : Circuit := ⟨[⟨.or, [4, 15]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [18, 6]⟩, ⟨.or, [20, 3]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [22, 7]⟩, ⟨.or, [23, 16]⟩, ⟨.or, [6, 19]⟩, ⟨.or, [25, 13]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [7, 19]⟩, ⟨.or, [28, 11]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [30, 12]⟩, ⟨.or, [31, 2]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [33, 17]⟩, ⟨.or, [18, 12]⟩, ⟨.or, [35, 7]⟩, ⟨.and, [24, 34]⟩, ⟨.and, [36, 27]⟩, ⟨.and, [26, 32]⟩, ⟨.and, [29, 21]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 39]⟩], 43⟩

/-- Boolean check: every gate is AND or OR and reads at most two wires. -/
def andOrTwo (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with
      | GateOp.and => true
      | GateOp.or => true
      | _ => false) && decide (g.inputs.length ≤ 2)

theorem andOrTwo_mono (C : Circuit) (h : andOrTwo C = true) : Monotone2 C := by
  intro g hg
  have hg' := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg'
  refine ⟨?_, hg'.2⟩
  cases hop : g.op <;> simp [hop] at hg' ⊢

theorem rep : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11914988824647881820 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨circ, andOrTwo_mono circ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20372

theorem PEqualNP.Outside.L_meta_20372 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11914988824647881820 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20372.rep
