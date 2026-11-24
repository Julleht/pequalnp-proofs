import PEqualNP.Defs

-- Cut of L-meta-3420: (normalize) every 14-step program yields a dominance-free trace of at most 14
-- genuine AND/OR steps over the seeds 0, all-ones and the ten inputs that contains the target 4095;
-- (search) no such dominance-free trace exists.  A word d dominates w when d has every edge row
-- (bits 0..11) of w and no independent-set row (bits 12..23) outside w.
theorem PEqualNP.Outside.R_meta_3420_1
    (normalize : ∀ x : List (BitVec 24), let I : List (BitVec 24) := [5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968, 5689661];
      x.length = 24 → x.take 10 = I → x.getD 23 0 = 4095 →
      (∀ j : ℕ, 0 < j → j < 15 → x.getD (9 + j) 0 = 16777215 ∨ ∃ u v : BitVec 24,
        u ∈ x.take (9 + j) ∧ v ∈ x.take (9 + j) ∧
          (x.getD (9 + j) 0 = u &&& v ∨ x.getD (9 + j) 0 = u ||| v)) →
      ∃ t : List (BitVec 24), let B : List (BitVec 24) := 0 :: 16777215 :: I;
      t.length ≤ 14 ∧ (4095 : BitVec 24) ∈ t ∧ ∀ (j : ℕ) (hj : j < t.length),
        (∀ d ∈ B ++ t.take j, ¬ ((t[j] &&& 4095) &&& ~~~d = 0 ∧ (d &&& ~~~t[j]) &&& 16773120 = 0)) ∧
        ∃ u ∈ B ++ t.take j, ∃ v ∈ B ++ t.take j, t[j] = u &&& v ∨ t[j] = u ||| v)
    (search : ¬ ∃ t : List (BitVec 24), let B : List (BitVec 24) := 0 :: 16777215 :: [5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968, 5689661];
      t.length ≤ 14 ∧ (4095 : BitVec 24) ∈ t ∧ ∀ (j : ℕ) (hj : j < t.length),
        (∀ d ∈ B ++ t.take j, ¬ ((t[j] &&& 4095) &&& ~~~d = 0 ∧ (d &&& ~~~t[j]) &&& 16773120 = 0)) ∧
        ∃ u ∈ B ++ t.take j, ∃ v ∈ B ++ t.take j, t[j] = u &&& v ∨ t[j] = u ||| v) :
    ¬∃ (x1 : List (BitVec (24 : ℕ))),     x1.length = (24 : ℕ) ∧       List.take (10 : ℕ) x1 = [(5521457 : BitVec (24 : ℕ)), (8532035 : BitVec (24 : ℕ)), (3227782 : BitVec (24 : ℕ)), (430348 : BitVec (24 : ℕ)), (11083800 : BitVec (24 : ℕ)), (113184 : BitVec (24 : ℕ)), (902208 : BitVec (24 : ℕ)), (13501056 : BitVec (24 : ℕ)), (15731968 : BitVec (24 : ℕ)), (5689661 : BitVec (24 : ℕ))] ∧         x1.getD (23 : ℕ) (0 : BitVec (24 : ℕ)) = (4095 : BitVec (24 : ℕ)) ∧           ((0 : BitVec (24 : ℕ)) :: x1).Nodup ∧             ∀ (x2 : ℕ),               (0 : ℕ) < x2 →                 x2 < (15 : ℕ) →                   have x5 : BitVec (24 : ℕ) := x1.getD ((9 : ℕ) + x2) (0 : BitVec (24 : ℕ));                   x5 = (16777215 : BitVec (24 : ℕ)) ∨ ∃ (x6 : BitVec (24 : ℕ)) (x7 : BitVec (24 : ℕ)), x6 ∈ List.take ((9 : ℕ) + x2) x1 ∧ x7 ∈ List.take ((9 : ℕ) + x2) x1 ∧ (x5 = x6 &&& x7 ∨ x5 = x6 ||| x7) := by
  rintro ⟨x, hlen, htake, hout, -, hstep⟩
  exact search (normalize x hlen htake hout hstep)
