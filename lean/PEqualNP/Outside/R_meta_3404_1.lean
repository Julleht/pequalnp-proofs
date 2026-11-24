import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3404_1
    (small : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (S : Finset (Fin 9)), PEqualNP.MetaComplexity.FanInTwo C → S.card ≤ 1 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ i ∈ S, x i = true)]) =
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) →
      14 ≤ C.size)
    (pair : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin 9), PEqualNP.MetaComplexity.FanInTwo C → a < b →
      1 ≤ PEqualNP.NotBracket.notCount C → PEqualNP.NotBracket.notCount C ≤ 2 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) =
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) →
      14 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (2 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x8 ∈ x2, x7 x8 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x8.1 && x7 x8.2) → (14 : ℕ) ≤ x1.size := by
  intro C S hf hc hn1 hn2 he
  by_cases h1 : S.card ≤ 1
  · exact small C S hf h1 he
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (show S.card = 2 by omega)
    have key : ∀ x : Fin 9 → Bool, decide (∃ i ∈ ({a, b} : Finset (Fin 9)), x i = true) = (x a || x b) := by
      intro x
      by_cases ha : x a = true <;> by_cases hb : x b = true <;> simp [ha, hb]
    rcases lt_or_gt_of_ne hab with h | h
    · refine pair C a b hf h hn1 hn2 (fun x => ?_)
      have hx := he x
      rw [key x] at hx
      exact hx
    · refine pair C b a hf h hn1 hn2 (fun x => ?_)
      have hx := he x
      rw [key x, Bool.or_comm (x a) (x b)] at hx
      exact hx
