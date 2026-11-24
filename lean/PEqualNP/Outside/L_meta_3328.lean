import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3328

def Op (S : List ℕ) (v : ℕ) : Prop := ∃ a ∈ S, ∃ b ∈ S, v = a &&& b ∨ v = a ||| b

def Good (S P : List ℕ) : Prop := ∀ i : Fin P.length, Op (S ++ List.take (↑i) P) (P.get i)

theorem op_mono {S T : List ℕ} {v : ℕ} (h : S ⊆ T) : Op S v → Op T v := by
  rintro ⟨a, ha, b, hb, e⟩
  exact ⟨a, h ha, b, h hb, e⟩

theorem good_mono {S T P : List ℕ} (h : S ⊆ T) : Good S P → Good T P := by
  intro hg i
  refine op_mono ?_ (hg i)
  intro x hx
  rw [List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (h hx)
  · exact Or.inr hx

theorem good_nil (S : List ℕ) : Good S [] := by
  intro i; exact i.elim0

theorem good_cons (S P : List ℕ) (a : ℕ) : Good S (a :: P) ↔ Op S a ∧ Good (a :: S) P := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h ⟨0, by simp⟩
      simpa using this
    · intro i
      have := h ⟨i.1 + 1, by simp⟩
      simp only [List.take_succ_cons, List.get_eq_getElem, List.getElem_cons_succ] at this
      refine op_mono ?_ this
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      tauto
  · rintro ⟨h0, h1⟩ i
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero => simpa using h0
    | succ i =>
      have := h1 ⟨i, by simpa using hi⟩
      simp only [List.take_succ_cons, List.get_eq_getElem, List.getElem_cons_succ] at this ⊢
      refine op_mono ?_ this
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      tauto

theorem good_append : ∀ (P S Q : List ℕ), Good S P → Good (S ++ P) Q → Good S (P ++ Q) := by
  intro P
  induction P with
  | nil => intro S Q _ h; simpa using h
  | cons a P ih =>
    intro S Q h1 h2
    rw [good_cons] at h1
    rw [List.cons_append, good_cons]
    refine ⟨h1.1, ih _ _ h1.2 ?_⟩
    refine good_mono ?_ h2
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    tauto

def clean : List ℕ → List ℕ → List ℕ
  | _, [] => []
  | seen, a :: l => if a ∈ seen then clean seen l else a :: clean (a :: seen) l

theorem clean_spec : ∀ (l seen : List ℕ), Good seen l →
    Good seen (clean seen l) ∧ (∀ x, x ∈ seen ++ clean seen l ↔ x ∈ seen ++ l) ∧
    (clean seen l).Nodup ∧ (∀ x ∈ clean seen l, x ∉ seen) ∧ (clean seen l).length ≤ l.length := by
  intro l
  induction l with
  | nil => intro seen _; simp [clean, good_nil]
  | cons a l ih =>
    intro seen hg
    rw [good_cons] at hg
    by_cases ha : a ∈ seen
    · have hsub : a :: seen ⊆ seen := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact hx
      obtain ⟨g, m, nd, dj, ln⟩ := ih seen (good_mono hsub hg.2)
      simp only [clean, ha, ite_true]
      refine ⟨g, ?_, nd, dj, by simp; omega⟩
      intro x
      rw [m]
      simp only [List.mem_append, List.mem_cons]
      constructor
      · tauto
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl ha
        · exact Or.inr h
    · obtain ⟨g, m, nd, dj, ln⟩ := ih (a :: seen) hg.2
      simp only [clean, ha, ite_false]
      refine ⟨(good_cons _ _ _).2 ⟨hg.1, g⟩, ?_, ?_, ?_, by simp; omega⟩
      · intro x
        have := m x
        simp only [List.mem_append, List.mem_cons] at this ⊢
        tauto
      · refine List.nodup_cons.2 ⟨?_, nd⟩
        intro hm
        exact dj a hm (List.mem_cons_self)
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ha
        · intro hs
          exact dj x hx (List.mem_cons_of_mem _ hs)

theorem main : ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → Op x3 x4 →
    Good (x4 :: x3) x6 → Op (x4 :: x3 ++ x6) x5 →
    ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧
      x5 ∈ x11 ∧ Good x3 x11 := by
  intro x3 x4 x5 x6 h5 h4 h6 hop
  have hL : Good x3 (x4 :: (x6 ++ [x5])) := by
    rw [good_cons]
    refine ⟨h4, good_append _ _ _ h6 ?_⟩
    rw [good_cons]
    exact ⟨hop, good_nil _⟩
  obtain ⟨g, m, nd, dj, ln⟩ := clean_spec _ x3 hL
  refine ⟨clean x3 (x4 :: (x6 ++ [x5])), ?_, nd, dj, ?_, g⟩
  · simp at ln; omega
  · have := (m x5).2 (by simp)
    rw [List.mem_append] at this
    rcases this with h | h
    · exact absurd h h5
    · exact h

end PEqualNP.Outside.L_meta_3328

theorem PEqualNP.Outside.L_meta_3328 : have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  intro x1 x2
  exact PEqualNP.Outside.L_meta_3328.main
