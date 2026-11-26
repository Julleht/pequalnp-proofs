import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20875

def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [8, 17]⟩, ⟨.and, [11, 18]⟩], 19⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : Monotone2 witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_20875

open PEqualNP.Outside.L_meta_20875 in
theorem PEqualNP.Outside.L_meta_20875 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31917089 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
