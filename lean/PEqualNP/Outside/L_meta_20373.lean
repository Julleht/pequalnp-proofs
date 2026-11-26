import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20373

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- An AND/OR circuit of 27 fan-in-two gates; wires 0-7 the left vertices, 8-15 the right. -/
def circ : Circuit := ⟨[⟨.or, [1, 8]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [18, 12]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [21, 0]⟩, ⟨.or, [19, 15]⟩, ⟨.or, [23, 17]⟩, ⟨.or, [24, 2]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [26, 0]⟩, ⟨.or, [27, 4]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [29, 7]⟩, ⟨.or, [30, 17]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [32, 12]⟩, ⟨.or, [33, 7]⟩, ⟨.or, [18, 4]⟩, ⟨.or, [35, 19]⟩, ⟨.or, [36, 11]⟩, ⟨.and, [22, 25]⟩, ⟨.and, [28, 34]⟩, ⟨.and, [31, 37]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [41, 38]⟩], 42⟩

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

theorem rep : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12602045345396281050 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨circ, andOrTwo_mono circ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20373

theorem PEqualNP.Outside.L_meta_20373 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12602045345396281050 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20373.rep
