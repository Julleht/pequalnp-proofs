import PEqualNP.Defs

-- L-meta-25670: with u = t = 0 the pairing set L is empty and K is all five rows, so the four-cell test must hold
-- for every pair under the full column matching; a finite check over the matchings with row 0 sent to
-- column 0 (the other four values range over Fin 5) shows each one fails on some pair.

namespace PEqualNP.Outside.L_meta_25670_aux

def Gm (i j : Fin 5) : Bool := (25298977 : ℕ).testBit (5 * i.val + j.val)

def bad (f : Fin 5 → Fin 5) (i j : Fin 5) : Bool :=
  Bool.xor (Bool.xor (Gm i (f i)) (Gm j (f j))) (Bool.xor (Gm i (f j)) (Gm j (f i)))

theorem key : ∀ a1 a2 a3 a4 : Fin 5,
    (∀ i j : Fin 5, i ≠ j → (![0, a1, a2, a3, a4] : Fin 5 → Fin 5) i ≠ ![0, a1, a2, a3, a4] j) →
    ∃ i j : Fin 5, bad ![0, a1, a2, a3, a4] i j = true := by
  decide

end PEqualNP.Outside.L_meta_25670_aux

open PEqualNP.Outside.L_meta_25670_aux in
theorem PEqualNP.Outside.L_meta_25670 :
    let G := fun (i j : Fin 5) => (25298977 : ℕ).testBit (5 * i.val + j.val)
    let u : ℕ := 0
    let t : ℕ := 0
    ¬ (∃ (π : Equiv.Perm (Fin 5)) (K L : Finset (Fin 5)),
        π 0 = 0 ∧ L ⊆ K ∧ L.card ≤ u ∧ 5 ≤ K.card + t ∧
        ∀ i ∈ K, ∀ j ∈ K,
          Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
          Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) := by
  intro G u t
  rintro ⟨π, K, L, h0, _, hLu, hK, hcond⟩
  have hL : L = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hLu)
  have hKu : K = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]
    have hK' : 5 ≤ K.card := hK
    have := Finset.card_le_univ K
    simp only [Fintype.card_fin] at this
    omega
  subst hL hKu
  have hf : (π : Fin 5 → Fin 5) = ![0, π 1, π 2, π 3, π 4] := by
    funext i; fin_cases i
    · exact h0
    all_goals rfl
  obtain ⟨i, j, hij⟩ := key (π 1) (π 2) (π 3) (π 4) (by
    rw [← hf]; intro i j hne heq; exact hne (π.injective heq))
  have hc := hcond i (Finset.mem_univ _) j (Finset.mem_univ _)
  simp only [Finset.notMem_empty, decide_false, Bool.xor_false] at hc
  rw [← hf] at hij
  have : bad π i j = false := hc
  rw [this] at hij
  exact Bool.false_ne_true hij
