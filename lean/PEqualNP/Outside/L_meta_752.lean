import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_752

def G : SimpleGraph (Fin 4) where
  Adj a b := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)
  symm := ⟨by
    intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp⟩
  loopless := ⟨by
    intro a h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all⟩

theorem adj_iff (a b : Fin 4) :
    G.Adj a b ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) :=
  Iff.rfl

theorem unique_nbr (v a b : Fin 4) (ha : G.Adj v a) (hb : G.Adj v b) : a = b := by
  rw [adj_iff] at ha hb
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all

theorem acyclic : G.IsAcyclic := by
  intro v c hc
  have h1 : G.Adj v c.snd := c.adj_snd hc.not_nil
  have h2 : G.Adj v c.penultimate := (c.adj_penultimate hc.not_nil).symm
  exact hc.snd_ne_penultimate (unique_nbr v _ _ h1 h2)

theorem has_edge : ∃ i j : Fin 4, G.Adj i j := ⟨0, 1, by simp [adj_iff]⟩

theorem cover_two : ∀ T : Finset (Fin 4), (∀ i j : Fin 4, G.Adj i j → i ∈ T ∨ j ∈ T) →
    2 ≤ T.card := by
  intro T hT
  have h01 := hT 0 1 (by simp [adj_iff])
  have h23 := hT 2 3 (by simp [adj_iff])
  have key : 1 < T.card := by
    rw [Finset.one_lt_card]
    rcases h01 with h0 | h1 <;> rcases h23 with h2 | h3
    · exact ⟨0, h0, 2, h2, by decide⟩
    · exact ⟨0, h0, 3, h3, by decide⟩
    · exact ⟨1, h1, 2, h2, by decide⟩
    · exact ⟨1, h1, 3, h3, by decide⟩
  omega

theorem fn_eq [DecidableRel G.Adj] :
    (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4, G.Adj i j ∧ x i = true ∧ x j = true)) =
      (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) := by
  funext x
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    rw [adj_iff] at hij
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hi, hj⟩
    · exact Or.inl ⟨hj, hi⟩
    · exact Or.inr ⟨hi, hj⟩
    · exact Or.inr ⟨hj, hi⟩
  · rintro (⟨h0, h1⟩ | ⟨h2, h3⟩)
    · exact ⟨0, 1, by simp [adj_iff], h0, h1⟩
    · exact ⟨2, 3, by simp [adj_iff], h2, h3⟩

theorem edge_card [DecidableRel G.Adj] : G.edgeFinset.card = 2 := by
  have h : G.edgeFinset = {s(0, 1), s(2, 3)} := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, adj_iff]
      simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk]
      omega
  rw [h]
  rfl

theorem size_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ}
    (h : PEqualNP.MetaComplexity.HasCircuitSize n f s) (hst : s ≤ t) :
    PEqualNP.MetaComplexity.HasCircuitSize n f t := by
  obtain ⟨C, hC, hs, he⟩ := h
  exact ⟨C, hC, le_trans hs hst, he⟩

end PEqualNP.Outside.L_meta_752

open PEqualNP.Outside.L_meta_752 in
theorem PEqualNP.Outside.L_meta_752 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) s ↔ 3 ≤ s := by
  classical
  intro s
  constructor
  · intro h
    rw [← fn_eq] at h
    have hb := PEqualNP.MetaComplexity.L104 4 2 s G acyclic has_edge cover_two h
    rw [edge_card] at hb
    omega
  · intro hs
    have hT : ∀ i j : Fin 4, G.Adj i j → i ∈ ({0, 2} : Finset (Fin 4)) ∨ j ∈ ({0, 2} : Finset (Fin 4)) := by
      intro i j hij
      rw [adj_iff] at hij
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    have hu := PEqualNP.MetaComplexity.L105 4 G {0, 2} has_edge hT
    rw [edge_card, fn_eq] at hu
    have hc : ({0, 2} : Finset (Fin 4)).card = 2 := by decide
    rw [hc] at hu
    exact size_mono hu hs
