import PEqualNP.Defs

-- L-lib-461: take D = C both ways. With no edge outside D the relation has no first step, so no closed walk;
-- an edge a-b with both ends outside D gives the closed walk a to b to a.

namespace PEqualNP.Outside.L_lib_461_aux
end PEqualNP.Outside.L_lib_461_aux

open PEqualNP.Outside.L_lib_461_aux in
theorem PEqualNP.Outside.L_lib_461 :
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
      (∃ C : Finset (Fin n), C.card ≤ k ∧ G.IsVertexCover (C : Set (Fin n))) ↔
      ∃ D : Finset (Fin n), D.card ≤ k ∧ ∀ x : Fin n,
        ¬ Relation.TransGen (fun a b : Fin n => a ∉ D ∧ b ∉ D ∧ G.Adj a b) x x
      := by
  intro n k G
  constructor
  · rintro ⟨C, hk, hC⟩
    refine ⟨C, hk, fun x hx => ?_⟩
    obtain ⟨b, ⟨hxC, hbC, hadj⟩, _⟩ := Relation.TransGen.head'_iff.mp hx
    rcases hC hadj with h | h
    · exact hxC (Finset.mem_coe.mp h)
    · exact hbC (Finset.mem_coe.mp h)
  · rintro ⟨D, hk, hD⟩
    refine ⟨D, hk, fun v w hadj => ?_⟩
    by_contra hcon
    simp only [not_or, Finset.mem_coe] at hcon
    exact hD v (Relation.TransGen.tail (Relation.TransGen.single ⟨hcon.1, hcon.2, hadj⟩)
      ⟨hcon.2, hcon.1, hadj.symm⟩)
