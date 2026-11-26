import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20247

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- An AND/OR circuit of 28 fan-in-two gates; wires 0-7 the left vertices, 8-15 the right. -/
def circ : Circuit := ⟨[⟨.or, [2, 14]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [21, 9]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [25, 16]⟩, ⟨.or, [26, 17]⟩, ⟨.or, [17, 1]⟩, ⟨.or, [28, 11]⟩, ⟨.or, [29, 14]⟩, ⟨.or, [30, 18]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [32, 15]⟩, ⟨.or, [19, 11]⟩, ⟨.or, [34, 16]⟩, ⟨.or, [35, 9]⟩, ⟨.and, [33, 36]⟩, ⟨.and, [22, 31]⟩, ⟨.and, [27, 20]⟩, ⟨.and, [23, 24]⟩, ⟨.or, [37, 39]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [42, 38]⟩], 43⟩

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

theorem rep : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3258023176858573800 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨circ, andOrTwo_mono circ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20247

theorem PEqualNP.Outside.L_meta_20247 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3258023176858573800 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20247.rep
