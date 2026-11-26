import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20358

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- An AND/OR circuit of 30 fan-in-two gates; wires 0-7 the left vertices, 8-15 the right. -/
def circ : Circuit := ⟨[⟨.or, [1, 13]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [18, 3]⟩, ⟨.or, [23, 15]⟩, ⟨.or, [24, 0]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [26, 16]⟩, ⟨.or, [27, 2]⟩, ⟨.or, [28, 14]⟩, ⟨.or, [18, 7]⟩, ⟨.or, [30, 20]⟩, ⟨.or, [10, 20]⟩, ⟨.or, [32, 16]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [34, 19]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [36, 7]⟩, ⟨.or, [37, 17]⟩, ⟨.and, [25, 38]⟩, ⟨.and, [29, 31]⟩, ⟨.and, [22, 35]⟩, ⟨.and, [33, 21]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [43, 42]⟩, ⟨.or, [44, 41]⟩], 45⟩

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

theorem rep : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17418911685824797215 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨circ, andOrTwo_mono circ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20358

theorem PEqualNP.Outside.L_meta_20358 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17418911685824797215 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20358.rep
