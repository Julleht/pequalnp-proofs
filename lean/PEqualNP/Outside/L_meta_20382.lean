import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20382

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- An AND/OR circuit of 29 fan-in-two gates; wires 0-7 the left vertices, 8-15 the right. -/
def circ : Circuit := ⟨[⟨.or, [1, 15]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [21, 17]⟩, ⟨.or, [20, 3]⟩, ⟨.or, [23, 19]⟩, ⟨.or, [24, 9]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [26, 18]⟩, ⟨.or, [6, 18]⟩, ⟨.or, [28, 4]⟩, ⟨.or, [29, 15]⟩, ⟨.or, [30, 17]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [32, 9]⟩, ⟨.or, [33, 16]⟩, ⟨.or, [16, 4]⟩, ⟨.or, [35, 19]⟩, ⟨.or, [36, 8]⟩, ⟨.and, [31, 25]⟩, ⟨.and, [27, 34]⟩, ⟨.and, [8, 7]⟩, ⟨.and, [22, 37]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [42, 38]⟩, ⟨.or, [43, 41]⟩], 44⟩

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

theorem rep : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13064884772727831990 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨circ, andOrTwo_mono circ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20382

theorem PEqualNP.Outside.L_meta_20382 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13064884772727831990 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20382.rep
