import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_261

open PEqualNP.MetaComplexity

/-- Occurrences of the input `i` among the leaves (the count used in the statement). -/
noncomputable def cnt {n : ℕ} (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

/-- The formula is a single leaf reading the input `i` (as in the statement). -/
def isLit {n : ℕ} (i : Fin n) (φ : DMFormula n) : Prop :=
  DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i)
    (fun _ _ _ _ => False) (fun _ _ _ _ => False) φ

/-- Some node has a leaf child whose input also occurs in its sibling (as in the statement). -/
def Red {n : ℕ} (φ : DMFormula n) : Prop :=
  DMFormula.rec (motive := fun _ => Prop) (fun (_ : Fin n) (_ : Bool) => False)
    (fun A B p q => p ∨ q ∨ (∃ i : Fin n, isLit i A ∧ 1 ≤ cnt i B) ∨
      (∃ i : Fin n, isLit i B ∧ 1 ≤ cnt i A))
    (fun A B p q => p ∨ q ∨ (∃ i : Fin n, isLit i A ∧ 1 ≤ cnt i B) ∨
      (∃ i : Fin n, isLit i B ∧ 1 ≤ cnt i A)) φ

/-- A constant or a formula. -/
def Rv {n : ℕ} : Bool ⊕ DMFormula n → (Fin n → Bool) → Bool
  | Sum.inl c, _ => c
  | Sum.inr ψ, x => ψ.eval x

def Rl {n : ℕ} : Bool ⊕ DMFormula n → ℕ
  | Sum.inl _ => 0
  | Sum.inr ψ => ψ.leaves

theorem Rl_inr {n : ℕ} (ψ : DMFormula n) : Rl (Sum.inr ψ : Bool ⊕ DMFormula n) = ψ.leaves := rfl

theorem leaves_and {n : ℕ} (A B : DMFormula n) : (DMFormula.and A B).leaves = A.leaves + B.leaves := rfl

theorem leaves_or {n : ℕ} (A B : DMFormula n) : (DMFormula.or A B).leaves = A.leaves + B.leaves := rfl

theorem leaves_lit {n : ℕ} (i : Fin n) (b : Bool) : (DMFormula.lit i b).leaves = 1 := rfl

def mkAnd {n : ℕ} : Bool ⊕ DMFormula n → Bool ⊕ DMFormula n → Bool ⊕ DMFormula n
  | Sum.inl a, Sum.inl b => Sum.inl (a && b)
  | Sum.inl a, Sum.inr ψ => if a then Sum.inr ψ else Sum.inl false
  | Sum.inr φ, Sum.inl b => if b then Sum.inr φ else Sum.inl false
  | Sum.inr φ, Sum.inr ψ => Sum.inr (DMFormula.and φ ψ)

def mkOr {n : ℕ} : Bool ⊕ DMFormula n → Bool ⊕ DMFormula n → Bool ⊕ DMFormula n
  | Sum.inl a, Sum.inl b => Sum.inl (a || b)
  | Sum.inl a, Sum.inr ψ => if a then Sum.inl true else Sum.inr ψ
  | Sum.inr φ, Sum.inl b => if b then Sum.inl true else Sum.inr φ
  | Sum.inr φ, Sum.inr ψ => Sum.inr (DMFormula.or φ ψ)

theorem mkAnd_eval {n : ℕ} (r s : Bool ⊕ DMFormula n) (x : Fin n → Bool) :
    Rv (mkAnd r s) x = (Rv r x && Rv s x) := by
  rcases r with a | φ <;> rcases s with b | ψ
  · rfl
  · cases a <;> simp [mkAnd, Rv]
  · cases b <;> simp [mkAnd, Rv]
  · simp [mkAnd, Rv, DMFormula.eval]

theorem mkOr_eval {n : ℕ} (r s : Bool ⊕ DMFormula n) (x : Fin n → Bool) :
    Rv (mkOr r s) x = (Rv r x || Rv s x) := by
  rcases r with a | φ <;> rcases s with b | ψ
  · rfl
  · cases a <;> simp [mkOr, Rv]
  · cases b <;> simp [mkOr, Rv]
  · simp [mkOr, Rv, DMFormula.eval]

theorem mkAnd_le {n : ℕ} (r s : Bool ⊕ DMFormula n) : Rl (mkAnd r s) ≤ Rl r + Rl s := by
  rcases r with a | φ <;> rcases s with b | ψ
  · simp [mkAnd, Rl]
  · cases a <;> simp [mkAnd, Rl]
  · cases b <;> simp [mkAnd, Rl]
  · simp [mkAnd, Rl, DMFormula.leaves]

theorem mkOr_le {n : ℕ} (r s : Bool ⊕ DMFormula n) : Rl (mkOr r s) ≤ Rl r + Rl s := by
  rcases r with a | φ <;> rcases s with b | ψ
  · simp [mkOr, Rl]
  · cases a <;> simp [mkOr, Rl]
  · cases b <;> simp [mkOr, Rl]
  · simp [mkOr, Rl, DMFormula.leaves]

/-- Set the input `i` to `c` and fold the constants away. -/
def restrict {n : ℕ} (i : Fin n) (c : Bool) : DMFormula n → Bool ⊕ DMFormula n
  | DMFormula.lit j b => if j = i then Sum.inl (if b then c else !c) else Sum.inr (DMFormula.lit j b)
  | DMFormula.and A B => mkAnd (restrict i c A) (restrict i c B)
  | DMFormula.or A B => mkOr (restrict i c A) (restrict i c B)

theorem restrict_eval {n : ℕ} (i : Fin n) (c : Bool) (x : Fin n → Bool) (hx : x i = c) :
    ∀ φ : DMFormula n, Rv (restrict i c φ) x = φ.eval x := by
  intro φ
  induction φ with
  | lit j b =>
    by_cases h : j = i
    · subst h
      simp [restrict, Rv, DMFormula.eval, hx]
    · simp [restrict, Rv, h]
  | and A B ihA ihB => rw [restrict, mkAnd_eval, ihA, ihB]; rfl
  | or A B ihA ihB => rw [restrict, mkOr_eval, ihA, ihB]; rfl

theorem leaves_pos {n : ℕ} (φ : DMFormula n) : 1 ≤ φ.leaves := by
  induction φ with
  | lit j b => simp [DMFormula.leaves]
  | and A B ihA _ => simp only [DMFormula.leaves]; omega
  | or A B ihA _ => simp only [DMFormula.leaves]; omega

theorem restrict_le {n : ℕ} (i : Fin n) (c : Bool) :
    ∀ φ : DMFormula n, Rl (restrict i c φ) ≤ φ.leaves := by
  intro φ
  induction φ with
  | lit j b =>
    by_cases h : j = i
    · simp [restrict, Rl, h, DMFormula.leaves]
    · simp [restrict, Rl, h, DMFormula.leaves]
  | and A B ihA ihB =>
    have := mkAnd_le (restrict i c A) (restrict i c B)
    simp only [restrict, DMFormula.leaves]
    omega
  | or A B ihA ihB =>
    have := mkOr_le (restrict i c A) (restrict i c B)
    simp only [restrict, DMFormula.leaves]
    omega

theorem restrict_lt {n : ℕ} (i : Fin n) (c : Bool) :
    ∀ φ : DMFormula n, 1 ≤ cnt i φ → Rl (restrict i c φ) < φ.leaves := by
  intro φ
  induction φ with
  | lit j b =>
    intro h
    by_cases hj : j = i
    · simp [restrict, Rl, hj, DMFormula.leaves]
    · simp [cnt, hj] at h
  | and A B ihA ihB =>
    intro h
    have hc : cnt i (DMFormula.and A B) = cnt i A + cnt i B := rfl
    have h1 := mkAnd_le (restrict i c A) (restrict i c B)
    have h2 := restrict_le i c A
    have h3 := restrict_le i c B
    simp only [restrict, DMFormula.leaves]
    by_cases hA : 1 ≤ cnt i A
    · have := ihA hA
      omega
    · have := ihB (by omega)
      omega
  | or A B ihA ihB =>
    intro h
    have hc : cnt i (DMFormula.or A B) = cnt i A + cnt i B := rfl
    have h1 := mkOr_le (restrict i c A) (restrict i c B)
    have h2 := restrict_le i c A
    have h3 := restrict_le i c B
    simp only [restrict, DMFormula.leaves]
    by_cases hA : 1 ≤ cnt i A
    · have := ihA hA
      omega
    · have := ihB (by omega)
      omega

theorem isLit_eq {n : ℕ} (i : Fin n) (A : DMFormula n) (h : isLit i A) :
    ∃ b : Bool, A = DMFormula.lit i b := by
  cases A with
  | lit j b =>
    have hj : j = i := h
    exact ⟨b, by rw [hj]⟩
  | and _ _ => exact absurd h id
  | or _ _ => exact absurd h id

theorem lit_eval {n : ℕ} (i : Fin n) (b : Bool) (x : Fin n → Bool) :
    (DMFormula.lit i b).eval x = decide (x i = b) := by
  cases b <;> cases hx : x i <;> simp [DMFormula.eval, hx]

theorem main {n : ℕ} : ∀ φ : DMFormula n, Red φ →
    ∃ r : Bool ⊕ DMFormula n, Rl r < φ.leaves ∧ ∀ x, Rv r x = φ.eval x := by
  intro φ
  induction φ with
  | lit j b => intro h; exact absurd h id
  | and A B ihA ihB =>
    intro h
    have h' : Red A ∨ Red B ∨ (∃ i : Fin n, isLit i A ∧ 1 ≤ cnt i B) ∨
        (∃ i : Fin n, isLit i B ∧ 1 ≤ cnt i A) := h
    have hA1 := leaves_pos A
    have hB1 := leaves_pos B
    rcases h' with hA | hB | ⟨i, hi, hc⟩ | ⟨i, hi, hc⟩
    · obtain ⟨r, hr, hv⟩ := ihA hA
      refine ⟨mkAnd r (Sum.inr B), ?_, fun x => ?_⟩
      · have := mkAnd_le r (Sum.inr B)
        simp only [Rl_inr, leaves_and, leaves_or, leaves_lit] at *
        omega
      · rw [mkAnd_eval, hv]; rfl
    · obtain ⟨r, hr, hv⟩ := ihB hB
      refine ⟨mkAnd (Sum.inr A) r, ?_, fun x => ?_⟩
      · have := mkAnd_le (Sum.inr A) r
        simp only [Rl_inr, leaves_and, leaves_or, leaves_lit] at *
        omega
      · rw [mkAnd_eval, hv]; rfl
    · obtain ⟨b, rfl⟩ := isLit_eq i A hi
      refine ⟨mkAnd (Sum.inr (DMFormula.lit i b)) (restrict i b B), ?_, fun x => ?_⟩
      · have := mkAnd_le (Sum.inr (DMFormula.lit i b)) (restrict i b B)
        have := restrict_lt i b B hc
        simp only [Rl_inr, leaves_and, leaves_or, leaves_lit] at *
        omega
      · rw [mkAnd_eval]
        show ((DMFormula.lit i b).eval x && Rv (restrict i b B) x) =
          ((DMFormula.lit i b).eval x && B.eval x)
        by_cases hx : x i = b
        · rw [restrict_eval i b x hx B]
        · rw [lit_eval]; simp [hx]
    · obtain ⟨b, rfl⟩ := isLit_eq i B hi
      refine ⟨mkAnd (restrict i b A) (Sum.inr (DMFormula.lit i b)), ?_, fun x => ?_⟩
      · have := mkAnd_le (restrict i b A) (Sum.inr (DMFormula.lit i b))
        have := restrict_lt i b A hc
        simp only [Rl_inr, leaves_and, leaves_or, leaves_lit] at *
        omega
      · rw [mkAnd_eval]
        show (Rv (restrict i b A) x && (DMFormula.lit i b).eval x) =
          (A.eval x && (DMFormula.lit i b).eval x)
        by_cases hx : x i = b
        · rw [restrict_eval i b x hx A]
        · rw [lit_eval]; simp [hx]
  | or A B ihA ihB =>
    intro h
    have h' : Red A ∨ Red B ∨ (∃ i : Fin n, isLit i A ∧ 1 ≤ cnt i B) ∨
        (∃ i : Fin n, isLit i B ∧ 1 ≤ cnt i A) := h
    have hA1 := leaves_pos A
    have hB1 := leaves_pos B
    rcases h' with hA | hB | ⟨i, hi, hc⟩ | ⟨i, hi, hc⟩
    · obtain ⟨r, hr, hv⟩ := ihA hA
      refine ⟨mkOr r (Sum.inr B), ?_, fun x => ?_⟩
      · have := mkOr_le r (Sum.inr B)
        simp only [Rl_inr, leaves_and, leaves_or, leaves_lit] at *
        omega
      · rw [mkOr_eval, hv]; rfl
    · obtain ⟨r, hr, hv⟩ := ihB hB
      refine ⟨mkOr (Sum.inr A) r, ?_, fun x => ?_⟩
      · have := mkOr_le (Sum.inr A) r
        simp only [Rl_inr, leaves_and, leaves_or, leaves_lit] at *
        omega
      · rw [mkOr_eval, hv]; rfl
    · obtain ⟨b, rfl⟩ := isLit_eq i A hi
      refine ⟨mkOr (Sum.inr (DMFormula.lit i b)) (restrict i (!b) B), ?_, fun x => ?_⟩
      · have := mkOr_le (Sum.inr (DMFormula.lit i b)) (restrict i (!b) B)
        have := restrict_lt i (!b) B hc
        simp only [Rl_inr, leaves_and, leaves_or, leaves_lit] at *
        omega
      · rw [mkOr_eval]
        show ((DMFormula.lit i b).eval x || Rv (restrict i (!b) B) x) =
          ((DMFormula.lit i b).eval x || B.eval x)
        by_cases hx : x i = b
        · rw [lit_eval]; simp [hx]
        · rw [restrict_eval i (!b) x (by cases b <;> simp_all) B]
    · obtain ⟨b, rfl⟩ := isLit_eq i B hi
      refine ⟨mkOr (restrict i (!b) A) (Sum.inr (DMFormula.lit i b)), ?_, fun x => ?_⟩
      · have := mkOr_le (restrict i (!b) A) (Sum.inr (DMFormula.lit i b))
        have := restrict_lt i (!b) A hc
        simp only [Rl_inr, leaves_and, leaves_or, leaves_lit] at *
        omega
      · rw [mkOr_eval]
        show (Rv (restrict i (!b) A) x || (DMFormula.lit i b).eval x) =
          (A.eval x || (DMFormula.lit i b).eval x)
        by_cases hx : x i = b
        · rw [lit_eval]; simp [hx]
        · rw [restrict_eval i (!b) x (by cases b <;> simp_all) A]

end PEqualNP.Outside.L_meta_261

open PEqualNP.Outside.L_meta_261 in
theorem PEqualNP.Outside.L_meta_261 : ∀ (n : ℕ) (φ : PEqualNP.MetaComplexity.DMFormula n), (∃ x y : Fin n → Bool, φ.eval x ≠ φ.eval y) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (_ : Fin n) (_ : Bool) => False) (fun A B p q => p ∨ q ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) A ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) B) ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) B ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) A)) (fun A B p q => p ∨ q ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) A ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) B) ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) B ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) A)) φ → ∃ ψ : PEqualNP.MetaComplexity.DMFormula n, ψ.leaves < φ.leaves ∧ ∀ x : Fin n → Bool, ψ.eval x = φ.eval x := by
  intro n φ hnc hred
  obtain ⟨r, hr, hv⟩ := main φ hred
  rcases r with c | ψ
  · obtain ⟨x, y, hxy⟩ := hnc
    exact absurd ((hv x).symm.trans (hv y)) hxy
  · exact ⟨ψ, hr, hv⟩
