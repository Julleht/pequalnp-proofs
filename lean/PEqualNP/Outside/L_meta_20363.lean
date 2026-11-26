import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20363

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- An AND/OR circuit of 28 fan-in-two gates; wires 0-7 the left vertices, 8-15 the right. -/
def circ : Circuit := ⟨[⟨.or, [7, 15]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [2, 17]⟩, ⟨.or, [21, 12]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [23, 11]⟩, ⟨.or, [24, 1]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [26, 17]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [28, 18]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [30, 1]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [32, 14]⟩, ⟨.or, [33, 3]⟩, ⟨.or, [16, 9]⟩, ⟨.or, [35, 4]⟩, ⟨.and, [34, 25]⟩, ⟨.and, [29, 27]⟩, ⟨.and, [36, 22]⟩, ⟨.and, [20, 31]⟩, ⟨.or, [37, 40]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [42, 39]⟩], 43⟩

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

theorem rep : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3937228359801398220 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨circ, andOrTwo_mono circ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20363

theorem PEqualNP.Outside.L_meta_20363 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3937228359801398220 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20363.rep
