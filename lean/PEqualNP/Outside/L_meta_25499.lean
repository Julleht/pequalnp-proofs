import Mathlib
import PEqualNP.Defs

-- Method: x ↦ x ^^^ d maps the slice of s bijectively onto the slice of s ^^^ d.setWidth b,
-- since setWidth commutes with xor. So the two biases add up to one sum over slice s of
-- sign(x) + sign(x ^^^ d), a term of absolute value 2 on agreements and 0 elsewhere.
-- The triangle inequality then bounds the absolute value by twice the agreement count.

theorem PEqualNP.Outside.L_meta_25499 : ∀ (k b : ℕ) (f : BitVec k → Bool) (d : BitVec k) (s : BitVec b),
  let slice := fun label : BitVec b =>
    Finset.univ.filter (fun key : BitVec k => key.setWidth b = label)
  let bias := fun t : BitVec b =>
    (slice t).sum (fun word => if f word then (-1 : ℤ) else 1)
  let agreements := (slice s).filter (fun x => f x = f (x ^^^ d))
  (bias s + bias (s ^^^ d.setWidth b)).natAbs ≤ 2 * agreements.card := by
  intro k b f d s slice bias agreements
  have hx : ∀ x : BitVec k, (x ^^^ d).setWidth b = x.setWidth b ^^^ d.setWidth b := by
    intro x
    ext i hi
    simp [BitVec.getElem_setWidth, BitVec.getLsbD_xor]
  have hb : bias (s ^^^ d.setWidth b)
      = (slice s).sum (fun x => if f (x ^^^ d) then (-1 : ℤ) else 1) := by
    symm
    apply Finset.sum_nbij' (fun x => x ^^^ d) (fun x => x ^^^ d)
    · intro x hmem
      simp only [slice, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
      rw [hx, hmem]
    · intro x hmem
      simp only [slice, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
      rw [hx, hmem, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    · intro x _
      simp [BitVec.xor_assoc]
    · intro x _
      simp [BitVec.xor_assoc]
    · intro x _
      rfl
  have hsum : bias s + bias (s ^^^ d.setWidth b)
      = (slice s).sum (fun x => (if f x then (-1 : ℤ) else 1) + (if f (x ^^^ d) then (-1 : ℤ) else 1)) := by
    rw [hb, ← Finset.sum_add_distrib]
  have hle : |bias s + bias (s ^^^ d.setWidth b)| ≤ 2 * (agreements.card : ℤ) := by
    rw [hsum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ x ∈ slice s,
        |(if f x then (-1 : ℤ) else 1) + (if f (x ^^^ d) then (-1 : ℤ) else 1)|
          ≤ if f x = f (x ^^^ d) then (2 : ℤ) else 0 := by
      intro x _
      cases f x <;> cases f (x ^^^ d) <;> simp
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [← Finset.sum_filter]
    simp [agreements, Finset.sum_const, mul_comm]
  have hcast : ((bias s + bias (s ^^^ d.setWidth b)).natAbs : ℤ) ≤ ((2 * agreements.card : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    push_cast
    exact hle
  exact_mod_cast hcast
