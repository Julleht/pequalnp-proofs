import PEqualNP.Defs

-- L-meta-25482: not a closed computation (k, u, v are universally quantified), so no kernel evaluation.
-- `List.any` over `List.range (2 ^ k)` is true exactly when some w < 2 ^ k makes the conjunction true;
-- rewriting with List.any_eq_true, List.mem_range, Bool.and_eq_true and decide_eq_true_eq closes the goal.

theorem PEqualNP.Outside.L_meta_25482 :
    ∀ (k : Nat) (u v : Fin (2 ^ k)),
      let rot := fun (s word : Nat) =>
        ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
      let cutoff := 2 ^ (k - (k + 1) / 2)
      (List.range (2 ^ k)).any (fun key =>
        decide ((rot 1 key ^^^ u.val) < cutoff) &&
        decide ((rot 3 key ^^^ v.val) < cutoff)) = true ↔
        ∃ w < 2 ^ k, (rot 1 w ^^^ u.val) < cutoff ∧ (rot 3 w ^^^ v.val) < cutoff := by
  intro k u v rot cutoff
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
