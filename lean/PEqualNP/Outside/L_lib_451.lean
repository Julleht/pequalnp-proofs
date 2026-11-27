import PEqualNP.Defs

-- L-lib-451: the private tag inl v lies only in the bag of v, so bags are injective. Two bags of distinct
-- vertices meet only in an edge tag of an edge between them, so they are disjoint exactly when the vertices
-- are not adjacent; images of an independent set and preimages of a packing give the two directions.

theorem PEqualNP.Outside.L_lib_451 :
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
      let bag : Fin n → Set (Fin n ⊕ (Fin n × Fin n)) := fun v =>
        {z | z = Sum.inl v ∨ ∃ a b : Fin n,
          z = Sum.inr (a, b) ∧ G.Adj a b ∧ (v = a ∨ v = b)}
      (∃ S : Finset (Fin n), k ≤ S.card ∧
        ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b) ↔
      ∃ T : Finset (Set (Fin n ⊕ (Fin n × Fin n))), k ≤ T.card ∧
        (∀ B ∈ T, ∃ v, B = bag v) ∧ ∀ B ∈ T, ∀ C ∈ T, B ≠ C → Disjoint B C
      := by
  intro n k G bag
  classical
  have hinl : ∀ v w : Fin n, Sum.inl v ∈ bag w ↔ v = w := by
    intro v w
    simp [bag]
  have hinr : ∀ v a b : Fin n, Sum.inr (a, b) ∈ bag v ↔ G.Adj a b ∧ (v = a ∨ v = b) := by
    intro v a b
    simp [bag]
  have hinj : ∀ v w : Fin n, bag v = bag w → v = w := by
    intro v w h
    have h1 : Sum.inl v ∈ bag w := by rw [← h]; exact (hinl v v).mpr rfl
    exact (hinl v w).mp h1
  constructor
  · rintro ⟨S, hk, hS⟩
    refine ⟨S.image bag, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (fun v w h => hinj v w h)]
      exact hk
    · intro B hB
      obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hB
      exact ⟨v, hv.symm⟩
    · intro B hB C hC hBC
      obtain ⟨a, ha, hBa⟩ := Finset.mem_image.mp hB
      obtain ⟨b, hb, hCb⟩ := Finset.mem_image.mp hC
      subst hBa hCb
      have hab : a ≠ b := by
        intro h
        exact hBC (by rw [h])
      rw [Set.disjoint_left]
      intro z hza hzb
      rcases z with v | ⟨x, y⟩
      · exact hab (((hinl v a).mp hza).symm.trans ((hinl v b).mp hzb))
      · obtain ⟨hxy, hax⟩ := (hinr a x y).mp hza
        obtain ⟨-, hbx⟩ := (hinr b x y).mp hzb
        rcases hax with h1 | h1 <;> rcases hbx with h2 | h2
        · exact hab (h1.trans h2.symm)
        · rw [← h1, ← h2] at hxy
          exact hS a ha b hb hxy
        · rw [← h1, ← h2] at hxy
          exact hS a ha b hb hxy.symm
        · exact hab (h1.trans h2.symm)
  · rintro ⟨T, hk, hT, hdisj⟩
    refine ⟨Finset.univ.filter (fun v => bag v ∈ T), ?_, ?_⟩
    · have hsub : T ⊆ (Finset.univ.filter (fun v => bag v ∈ T)).image bag := by
        intro B hB
        obtain ⟨v, hv⟩ := hT B hB
        subst hv
        exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩, rfl⟩
      calc k ≤ T.card := hk
        _ ≤ _ := Finset.card_le_card hsub
        _ ≤ _ := Finset.card_image_le
    · intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hne : a ≠ b := by
        intro h
        rw [h] at hab
        exact G.irrefl hab
      have hbne : bag a ≠ bag b := fun h => hne (hinj a b h)
      have hd := hdisj _ ha' _ hb' hbne
      exact Set.disjoint_left.mp hd ((hinr a a b).mpr ⟨hab, Or.inl rfl⟩)
        ((hinr b a b).mpr ⟨hab, Or.inr rfl⟩)
