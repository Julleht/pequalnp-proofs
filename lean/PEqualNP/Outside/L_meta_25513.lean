import PEqualNP.Defs

-- L-meta-25513: forward, each ordered point (u,v) adds at most one conjunction: a true diagonal
-- point adds (P_u,P_u) to B, a false point adds its pair term to H, a true point adds it to A, or to
-- B when only the reverse point has an exposed index. The pair term is (R_u,P_v) or (C_v,P_u) when
-- exposed, else (P_u,P_v). Backward: an uncovered asymmetric pair has equal signal sets both ways.

namespace PEqualNP.Outside.L_meta_25513_aux

def sig {n : ℕ} (rows cols : Finset (Fin n)) (u v : Fin n) : Finset (Fin 3 × Fin n) :=
  (Finset.univ : Finset (Fin 3 × Fin n)).filter (fun s =>
      if s.1 = 0 then s.2 = u ∨ s.2 = v
      else if s.1 = 1 then s.2 ∈ rows ∧ s.2 = u
      else s.2 ∈ cols ∧ s.2 = v)

def hitT {n : ℕ} (rows cols : Finset (Fin n)) (T : Finset ((Fin 3 × Fin n) × (Fin 3 × Fin n)))
    (u v : Fin n) : Prop :=
  ∃ t ∈ T, t.1 ∈ sig rows cols u v ∧ t.2 ∈ sig rows cols u v

theorem mem0 {n : ℕ} (rows cols : Finset (Fin n)) (u v i : Fin n) :
    ((0 : Fin 3), i) ∈ sig rows cols u v ↔ i = u ∨ i = v := by
  simp [sig]

theorem mem1 {n : ℕ} (rows cols : Finset (Fin n)) (u v i : Fin n) :
    ((1 : Fin 3), i) ∈ sig rows cols u v ↔ i ∈ rows ∧ i = u := by
  simp [sig]

theorem mem2 {n : ℕ} (rows cols : Finset (Fin n)) (u v i : Fin n) :
    ((2 : Fin 3), i) ∈ sig rows cols u v ↔ i ∈ cols ∧ i = v := by
  simp [sig]

def term {n : ℕ} (rows cols : Finset (Fin n)) (p : Fin n × Fin n) :
    (Fin 3 × Fin n) × (Fin 3 × Fin n) :=
  if p.1 = p.2 then ((0, p.1), (0, p.1))
  else if p.1 ∈ rows then ((1, p.1), (0, p.2))
  else if p.2 ∈ cols then ((2, p.2), (0, p.1))
  else ((0, p.1), (0, p.2))

def hitP {n : ℕ} (rows cols : Finset (Fin n)) (p : Fin n × Fin n) (x y : Fin n) : Prop :=
  (term rows cols p).1 ∈ sig rows cols x y ∧ (term rows cols p).2 ∈ sig rows cols x y

theorem hitP_cases {n : ℕ} (rows cols : Finset (Fin n)) (a b x y : Fin n)
    (h : hitP rows cols (a, b) x y) :
    (a = b ∧ (a = x ∨ a = y)) ∨ (a ≠ b ∧ a = x ∧ b = y) ∨
      (a ≠ b ∧ a ∉ rows ∧ b ∉ cols ∧ a = y ∧ b = x) := by
  unfold hitP term at h
  by_cases hab : a = b
  · subst hab
    simp only [if_true, mem0] at h
    exact Or.inl ⟨rfl, h.1⟩
  · simp only [hab, if_false] at h
    by_cases ha : a ∈ rows
    · simp only [ha, if_true, mem1, mem0] at h
      obtain ⟨⟨-, h1⟩, h2 | h2⟩ := h
      · exact absurd (h2.trans h1.symm).symm hab
      · exact Or.inr (Or.inl ⟨hab, h1, h2⟩)
    · simp only [ha, if_false] at h
      by_cases hb : b ∈ cols
      · simp only [hb, if_true, mem2, mem0] at h
        obtain ⟨⟨-, h1⟩, h2 | h2⟩ := h
        · exact Or.inr (Or.inl ⟨hab, h2, h1⟩)
        · exact absurd (h2.trans h1.symm) hab
      · simp only [hb, if_false, mem0] at h
        obtain ⟨h1 | h1, h2 | h2⟩ := h
        · exact absurd (h1.trans h2.symm) hab
        · exact Or.inr (Or.inl ⟨hab, h1, h2⟩)
        · exact Or.inr (Or.inr ⟨hab, ha, hb, h1, h2⟩)
        · exact absurd (h1.trans h2.symm) hab

theorem hit_self {n : ℕ} (rows cols : Finset (Fin n)) (a b : Fin n) (hab : a ≠ b) :
    hitP rows cols (a, b) a b := by
  unfold hitP term
  simp only [hab, if_false]
  by_cases ha : a ∈ rows
  · simp only [ha, if_true, mem1, mem0]
    simp [ha]
  · simp only [ha, if_false]
    by_cases hb : b ∈ cols
    · simp only [hb, if_true, mem2, mem0]
      simp [hb]
    · simp only [hb, if_false, mem0]
      simp

theorem hit_diag {n : ℕ} (rows cols : Finset (Fin n)) (a : Fin n) :
    hitP rows cols (a, a) a a := by
  unfold hitP term
  simp only [if_true, mem0]
  simp

def clA {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (p : Fin n × Fin n) :
    Prop :=
  p.1 ≠ p.2 ∧ G p.1 p.2 = true ∧ (G p.2 p.1 = true ∨ p.1 ∈ rows ∨ p.2 ∈ cols)

def clB {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (p : Fin n × Fin n) :
    Prop :=
  (p.1 = p.2 ∧ G p.1 p.1 = true) ∨
    (p.1 ≠ p.2 ∧ G p.1 p.2 = true ∧ G p.2 p.1 = false ∧ p.1 ∉ rows ∧ p.2 ∉ cols)

def clH {n : ℕ} (G : Fin n → Fin n → Bool) (p : Fin n × Fin n) : Prop :=
  p.1 ≠ p.2 ∧ G p.1 p.2 = false

theorem hit_image {n : ℕ} (rows cols : Finset (Fin n)) (P : Fin n × Fin n → Prop)
    [DecidablePred P] (x y : Fin n) :
    hitT rows cols ((Finset.univ.filter P).image (term rows cols)) x y ↔
      ∃ a b, P (a, b) ∧ hitP rows cols (a, b) x y := by
  unfold hitT hitP
  constructor
  · rintro ⟨t, ht, hq⟩
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.1 ht
    exact ⟨a, b, (Finset.mem_filter.1 hp).2, hq⟩
  · rintro ⟨a, b, hp, hq⟩
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩), hq⟩

theorem A_char {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (x y : Fin n)
    (h : ∃ a b, clA G rows cols (a, b) ∧ hitP rows cols (a, b) x y) :
    x ≠ y ∧ G x y = true ∧ (G y x = true ∨ x ∈ rows ∨ y ∈ cols) := by
  obtain ⟨a, b, hc, hp⟩ := h
  unfold clA at hc
  rcases hitP_cases rows cols a b x y hp with ⟨hab, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, ha, hb, rfl, rfl⟩
  · exact absurd hab hc.1
  · exact hc
  · refine ⟨fun e => hc.1 e.symm, ?_, Or.inl hc.2.1⟩
    rcases hc.2.2 with h | h | h
    · exact h
    · exact absurd h ha
    · exact absurd h hb

theorem H_char {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (x y : Fin n)
    (h : ∃ a b, clH G (a, b) ∧ hitP rows cols (a, b) x y) :
    x ≠ y ∧ (G x y = false ∨ (G y x = false ∧ y ∉ rows ∧ x ∉ cols)) := by
  obtain ⟨a, b, hc, hp⟩ := h
  unfold clH at hc
  rcases hitP_cases rows cols a b x y hp with ⟨hab, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, ha, hb, rfl, rfl⟩
  · exact absurd hab hc.1
  · exact ⟨hc.1, Or.inl hc.2⟩
  · exact ⟨fun e => hc.1 e.symm, Or.inr ⟨hc.2, ha, hb⟩⟩

theorem B_diag {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (x : Fin n)
    (h : ∃ a b, clB G rows cols (a, b) ∧ hitP rows cols (a, b) x x) : G x x = true := by
  obtain ⟨a, b, hc, hp⟩ := h
  rcases hitP_cases rows cols a b x x hp with ⟨rfl, h | h⟩ | ⟨hab, rfl, rfl⟩ | ⟨hab, -, -, rfl, rfl⟩
  · subst h
    rcases hc with h | h
    · exact h.2
    · exact absurd rfl h.1
  · subst h
    rcases hc with h | h
    · exact h.2
    · exact absurd rfl h.1
  · exact absurd rfl hab
  · exact absurd rfl hab

theorem point_le {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n))
    [DecidablePred (clA G rows cols)] [DecidablePred (clB G rows cols)] [DecidablePred (clH G)]
    (p : Fin n × Fin n) :
    (if clA G rows cols p then 1 else 0) + (if clB G rows cols p then 1 else 0) +
      (if clH G p then 1 else 0) ≤ 1 := by
  obtain ⟨a, b⟩ := p
  by_cases hA : clA G rows cols (a, b)
  · have hB : ¬ clB G rows cols (a, b) := by
      unfold clA at hA; unfold clB
      rintro (h | h)
      · exact hA.1 h.1
      · rcases hA.2.2 with e | e | e
        · rw [h.2.2.1] at e; exact absurd e (by decide)
        · exact h.2.2.2.1 e
        · exact h.2.2.2.2 e
    have hH : ¬ clH G (a, b) := by
      unfold clA at hA; unfold clH
      intro h; rw [h.2] at hA; exact absurd hA.2.1 (by decide)
    simp only [hA, hB, hH, if_true, if_false]; omega
  · by_cases hB : clB G rows cols (a, b)
    · have hH : ¬ clH G (a, b) := by
        unfold clB at hB; unfold clH
        rintro ⟨h1, h2⟩
        rcases hB with h | h
        · exact h1 h.1
        · rw [h2] at h; exact absurd h.2.1 (by decide)
      simp only [hA, hB, hH, if_true, if_false]; omega
    · simp only [hA, hB, if_false]; split_ifs <;> omega

theorem main_aux (n : ℕ) (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) :
    (∀ i j, G i j = true → G j i = false → i ∈ rows ∨ j ∈ cols ∨ j ∈ rows ∨ i ∈ cols) ↔
      ∃ A B H : Finset ((Fin 3 × Fin n) × (Fin 3 × Fin n)),
        A.card + B.card + H.card ≤ n * n ∧
        ∀ u v, G u v = true ↔
          (hitT rows cols A u v ∨ (hitT rows cols B u v ∧ ¬ hitT rows cols H u v)) := by
  classical
  constructor
  · intro hc
    refine ⟨(Finset.univ.filter (clA G rows cols)).image (term rows cols),
      (Finset.univ.filter (clB G rows cols)).image (term rows cols),
      (Finset.univ.filter (clH G)).image (term rows cols), ?_, ?_⟩
    · have h1 := Finset.card_image_le (s := Finset.univ.filter (clA G rows cols)) (f := term rows cols)
      have h2 := Finset.card_image_le (s := Finset.univ.filter (clB G rows cols)) (f := term rows cols)
      have h3 := Finset.card_image_le (s := Finset.univ.filter (clH G)) (f := term rows cols)
      have hs : (Finset.univ.filter (clA G rows cols)).card + (Finset.univ.filter (clB G rows cols)).card
          + (Finset.univ.filter (clH G)).card ≤ n * n := by
        rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        calc _ ≤ ∑ _p : Fin n × Fin n, 1 := Finset.sum_le_sum (fun p _ => point_le G rows cols p)
          _ = n * n := by simp
      omega
    · intro x y
      rw [hit_image, hit_image, hit_image]
      by_cases hxy : x = y
      · subst hxy
        constructor
        · intro h
          refine Or.inr ⟨⟨x, x, Or.inl ⟨rfl, h⟩, hit_diag rows cols x⟩, fun hH => ?_⟩
          exact (H_char G rows cols x x hH).1 rfl
        · rintro (hA | ⟨hB, -⟩)
          · exact absurd rfl (A_char G rows cols x x hA).1
          · exact B_diag G rows cols x hB
      · cases hg : G x y
        · constructor
          · intro h; exact absurd h (by decide)
          · rintro (hA | ⟨-, hH⟩)
            · have := (A_char G rows cols x y hA).2.1
              rw [hg] at this; exact absurd this (by decide)
            · exact absurd ⟨x, y, ⟨hxy, hg⟩, hit_self rows cols x y hxy⟩ hH
        · simp only [true_iff]
          by_cases hr : G y x = true ∨ x ∈ rows ∨ y ∈ cols
          · exact Or.inl ⟨x, y, ⟨hxy, hg, hr⟩, hit_self rows cols x y hxy⟩
          · have hyx : G y x = false := by
              cases e : G y x
              · rfl
              · exact absurd (Or.inl e) hr
            have hxr : x ∉ rows := fun e => hr (Or.inr (Or.inl e))
            have hyc : y ∉ cols := fun e => hr (Or.inr (Or.inr e))
            refine Or.inr ⟨⟨x, y, Or.inr ⟨hxy, hg, hyx, hxr, hyc⟩, hit_self rows cols x y hxy⟩,
              fun hH => ?_⟩
            rcases (H_char G rows cols x y hH).2 with e | ⟨-, hyr, hxc⟩
            · rw [hg] at e; exact absurd e (by decide)
            · rcases hc x y hg hyx with e | e | e | e
              · exact hxr e
              · exact hyc e
              · exact hyr e
              · exact hxc e
  · rintro ⟨A, B, H, -, hG⟩ i j hij hji
    by_contra hno
    have hs : sig rows cols i j = sig rows cols j i := by
      ext s
      obtain ⟨k, m⟩ := s
      unfold sig
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs
      · exact Or.comm
      · constructor
        · rintro ⟨h, rfl⟩; exact absurd (Or.inl h) hno
        · rintro ⟨h, rfl⟩; exact absurd (Or.inr (Or.inr (Or.inl h))) hno
      · constructor
        · rintro ⟨h, rfl⟩; exact absurd (Or.inr (Or.inl h)) hno
        · rintro ⟨h, rfl⟩; exact absurd (Or.inr (Or.inr (Or.inr h))) hno
    have e : ∀ T, hitT rows cols T i j ↔ hitT rows cols T j i := by
      intro T; unfold hitT; rw [hs]
    have h1 := (hG i j).1 hij
    rw [e A, e B, e H, ← hG j i, hji] at h1
    exact absurd h1 (by decide)

end PEqualNP.Outside.L_meta_25513_aux

open PEqualNP.Outside.L_meta_25513_aux in
theorem PEqualNP.Outside.L_meta_25513 :
    ∀ (n : ℕ) (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)),
      let signals := fun (u v : Fin n) =>
        (Finset.univ : Finset (Fin 3 × Fin n)).filter (fun s =>
          if s.1 = 0 then s.2 = u ∨ s.2 = v
          else if s.1 = 1 then s.2 ∈ rows ∧ s.2 = u
          else s.2 ∈ cols ∧ s.2 = v)
      let covers := ∀ i j, G i j = true → G j i = false →
        i ∈ rows ∨ j ∈ cols ∨ j ∈ rows ∨ i ∈ cols
      let hit := fun (T : Finset ((Fin 3 × Fin n) × (Fin 3 × Fin n)))
          (u v : Fin n) =>
        ∃ t ∈ T, t.1 ∈ signals u v ∧ t.2 ∈ signals u v
      covers ↔ ∃ A B H : Finset ((Fin 3 × Fin n) × (Fin 3 × Fin n)),
        A.card + B.card + H.card ≤ n * n ∧
        ∀ u v, G u v = true ↔ (hit A u v ∨ (hit B u v ∧ ¬ hit H u v)) := by
  intro n G rows cols
  exact main_aux n G rows cols
