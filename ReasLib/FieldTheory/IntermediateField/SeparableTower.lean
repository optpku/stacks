module

public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.IntermediateField.GeneratorTower

@[expose] public section

open IntermediateField

noncomputable section

universe u v w

namespace FieldExtension

section

variable (F : Type u) (K : Type v)
variable [Field F] [Field K] [Algebra F K]
variable {n : ℕ}

/-- A finite-generator stage is separable over the base when every preceding generator is
separable over its own preceding stage. -/
theorem adjoinStage_isSeparable
    (α : Fin n → K)
    (hsep : ∀ i : Fin n, IsSeparable (adjoinStage F α i.castSucc) (α i))
    (m : ℕ) (hm : m ≤ n) :
    Algebra.IsSeparable F (adjoinStage F α ⟨m, Nat.lt_succ_of_le hm⟩) := by
  induction m with
  | zero =>
      have hzero : adjoinStage F α ⟨0, Nat.lt_succ_of_le hm⟩ =
          (⊥ : IntermediateField F K) := by
        simpa using adjoinStage_zero (F := F) α
      rw [hzero]
      exact AlgEquiv.Algebra.isSeparable ((IntermediateField.botEquiv F K).symm)
  | succ m ih =>
      let i : Fin n := ⟨m, Nat.lt_of_succ_le hm⟩
      have hprev : Algebra.IsSeparable F (adjoinStage F α i.castSucc) :=
        ih (Nat.le_of_succ_le hm)
      have hnext : Algebra.IsSeparable (adjoinStage F α i.castSucc)
          ↥(IntermediateField.adjoin (adjoinStage F α i.castSucc) ({α i} : Set K)) := by
        simpa using
          (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
            (F := adjoinStage F α i.castSucc) (E := K) (x := α i)).2 (hsep i)
      rw [show adjoinStage F α ⟨m + 1, Nat.lt_succ_of_le hm⟩ =
          adjoinStage F α i.succ by rfl]
      rw [adjoinStage_succ (F := F) α i]
      change Algebra.IsSeparable F
        ↥(IntermediateField.adjoin (adjoinStage F α i.castSucc) ({α i} : Set K))
      -- Local instance justification (proof-local temporary data): compose the separable simple-adjoin extension with the preceding separable generator stage.
      letI : Algebra.IsSeparable (adjoinStage F α i.castSucc)
          ↥(IntermediateField.adjoin (adjoinStage F α i.castSucc) ({α i} : Set K)) := hnext
      exact Algebra.IsSeparable.trans F (adjoinStage F α i.castSucc)
        ↥(IntermediateField.adjoin (adjoinStage F α i.castSucc) ({α i} : Set K))

/-- A finite-generator tower spanning `K/F` is separable when each generator is separable over
the preceding stage. -/
theorem adjoinTower_isSeparable
    (α : Fin n → K) (hspan : adjoinStage F α (Fin.last n) = ⊤)
    (hsep : ∀ i : Fin n, IsSeparable (adjoinStage F α i.castSucc) (α i)) :
    Algebra.IsSeparable F K := by
  have hlast : Algebra.IsSeparable F (adjoinStage F α (Fin.last n)) :=
    adjoinStage_isSeparable F K α hsep n le_rfl
  let eTop : adjoinStage F α (Fin.last n) ≃ₐ[F] K :=
    (IntermediateField.equivOfEq hspan).trans IntermediateField.topEquiv
  exact AlgEquiv.Algebra.isSeparable eTop

end

section

variable (F : Type u) (K : Type v)
variable [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K]
variable {n : ℕ}

/-- The product of the separable degrees of the first `m` simple extensions in a finite
generator tower. -/
private abbrev adjoinStage.setNatSepDegreeProduct (α : Fin n → K) (m : ℕ) : ℕ :=
  ∏ j ∈ Finset.range m,
    if hj : j < n then
      (minpoly (adjoinStage F α (Fin.castSucc ⟨j, hj⟩)) (α ⟨j, hj⟩)).natSepDegree
    else 1

/-- Passing from one finite-generator stage to its successor multiplies the separable degree by
the separable degree of the next minimal polynomial. -/
private theorem adjoinStage_finSepDegree_succ (α : Fin n → K) (i : Fin n) :
    Field.finSepDegree F (adjoinStage F α i.succ) =
      Field.finSepDegree F (adjoinStage F α i.castSucc) *
        (minpoly (adjoinStage F α i.castSucc) (α i)).natSepDegree := by
  let M := IntermediateField.adjoin (adjoinStage F α i.castSucc) ({α i} : Set K)
  let halg : IsAlgebraic (adjoinStage F α i.castSucc) (α i) :=
    ((Algebra.IsIntegral.of_finite (adjoinStage F α i.castSucc) K).isIntegral
      (α i)).isAlgebraic
  have hstep : Field.finSepDegree (adjoinStage F α i.castSucc) M =
      (minpoly (adjoinStage F α i.castSucc) (α i)).natSepDegree := by
    simpa [M] using
      (IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree
        (F := adjoinStage F α i.castSucc) (E := K) halg)
  have hstage : adjoinStage F α i.succ = M.restrictScalars F := by
    exact adjoinStage_succ (F := F) α i
  rw [hstage]
  calc
    Field.finSepDegree F M =
        Field.finSepDegree F (adjoinStage F α i.castSucc) *
          Field.finSepDegree (adjoinStage F α i.castSucc) M := by
      symm
      exact Field.finSepDegree_mul_finSepDegree_of_isAlgebraic F
        (adjoinStage F α i.castSucc) M
    _ = Field.finSepDegree F (adjoinStage F α i.castSucc) *
          (minpoly (adjoinStage F α i.castSucc) (α i)).natSepDegree := by
      rw [hstep]

/-- The separable degree of a finite-generator stage is the product of the separable degrees of
the minimal polynomials adjoined before it. -/
private theorem adjoinStage_finSepDegree_prod (α : Fin n → K) :
    ∀ m : ℕ, ∀ hm : m ≤ n,
      Field.finSepDegree F (adjoinStage F α ⟨m, Nat.lt_succ_of_le hm⟩) =
        adjoinStage.setNatSepDegreeProduct F K α m
  | 0, hm => by
      have hzero : adjoinStage F α ⟨0, Nat.lt_succ_of_le hm⟩ =
          (⊥ : IntermediateField F K) := by
        simpa using adjoinStage_zero (F := F) α
      rw [hzero]
      simp [adjoinStage.setNatSepDegreeProduct]
  | m + 1, hm => by
      let i : Fin n := ⟨m, Nat.lt_of_succ_le hm⟩
      calc
        Field.finSepDegree F (adjoinStage F α ⟨m + 1, Nat.lt_succ_of_le hm⟩) =
            Field.finSepDegree F (adjoinStage F α i.succ) := by
          rfl
        _ = Field.finSepDegree F (adjoinStage F α i.castSucc) *
              (minpoly (adjoinStage F α i.castSucc) (α i)).natSepDegree :=
            adjoinStage_finSepDegree_succ F K α i
        _ = Field.finSepDegree F
              (adjoinStage F α ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩) *
              (minpoly (adjoinStage F α i.castSucc) (α i)).natSepDegree := by
          rfl
        _ = adjoinStage.setNatSepDegreeProduct F K α m *
              (minpoly (adjoinStage F α i.castSucc) (α i)).natSepDegree := by
          rw [adjoinStage_finSepDegree_prod α m (Nat.le_of_succ_le hm)]
        _ = adjoinStage.setNatSepDegreeProduct F K α (m + 1) := by
          simp [adjoinStage.setNatSepDegreeProduct, Finset.prod_range_succ, i,
            Nat.lt_of_succ_le hm]

/-- Lemma 9.12.9 (Tag 09H8): the finite separable degree of a field extension generated by a
finite tower is the product of the separable degrees of the successive minimal polynomials. -/
theorem adjoinTower_finSepDegree_prod (α : Fin n → K)
    (hspan : adjoinStage F α (Fin.last n) = ⊤) :
    Field.finSepDegree F K =
      ∏ i : Fin n, (minpoly (adjoinStage F α i.castSucc) (α i)).natSepDegree := by
  calc
    Field.finSepDegree F K = Field.finSepDegree F (adjoinStage F α (Fin.last n)) := by
      rw [hspan, IntermediateField.finSepDegree_top]
    _ = adjoinStage.setNatSepDegreeProduct F K α n := by
      have hlast : (Fin.last n : Fin (n + 1)) =
          ⟨n, Nat.lt_succ_of_le (le_rfl : n ≤ n)⟩ := Fin.ext rfl
      rw [hlast]
      exact adjoinStage_finSepDegree_prod F K α n le_rfl
    _ = ∏ i : Fin n, (minpoly (adjoinStage F α i.castSucc) (α i)).natSepDegree := by
      simpa [adjoinStage.setNatSepDegreeProduct] using
        (Fin.prod_univ_eq_prod_range
          (fun j : ℕ => if hj : j < n then
            (minpoly (adjoinStage F α (Fin.castSucc ⟨j, hj⟩))
              (α ⟨j, hj⟩)).natSepDegree else 1) n).symm

end

section

variable (F : Type u) (K : Type v) (L : Type w)
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [IsAlgClosed L]
variable [FiniteDimensional F K]
variable {n : ℕ}

/-- For a finite-generator tower spanning `K/F`, maps into an algebraically closed target are
counted by the product of the separable degrees of the successive minimal polynomials. -/
theorem adjoinTower_card_algHom_prod (α : Fin n → K)
    (hspan : adjoinStage F α (Fin.last n) = ⊤) :
    Nat.card (K →ₐ[F] L) =
      ∏ i : Fin n, (minpoly (adjoinStage F α i.castSucc) (α i)).natSepDegree := by
  rw [← Field.finSepDegree_eq_of_isAlgClosed F K L]
  exact adjoinTower_finSepDegree_prod F K α hspan

end

section

variable (F : Type u) (K : Type v) (L : Type w)
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [IsAlgClosed L]
variable {n : ℕ}

/-- Lemma 9.12.10 (Tag 09H9) (1): a spanning finite generator tower with separable successive
generators has as many maps into any algebraically closed target as its degree. -/
theorem adjoinTower_card_algHom_eq_finrank
    (α : Fin n → K) (hspan : adjoinStage F α (Fin.last n) = ⊤)
    (hsep : ∀ i : Fin n, IsSeparable (adjoinStage F α i.castSucc) (α i)) :
    Nat.card (K →ₐ[F] L) = Module.finrank F K := by
  have hKsep : Algebra.IsSeparable F K :=
    adjoinTower_isSeparable F K α hspan hsep
  rw [← Field.finSepDegree_eq_of_isAlgClosed F K L]
  simpa using Field.finSepDegree_eq_finrank_of_isSeparable F K

end

section

variable (F : Type u) (K : Type v) (L : Type w)
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [IsAlgClosed L]
variable [FiniteDimensional F K]
variable {n : ℕ}

/-- Lemma 9.12.10 (3): if a generator is inseparable over its preceding stage, maps into an
algebraically closed target are strictly fewer than the extension degree. -/
theorem adjoinTower_card_algHom_lt_finrank
    (α : Fin n → K)
    (hinsep : ∃ i : Fin n, ¬ IsSeparable (adjoinStage F α i.castSucc) (α i)) :
    Nat.card (K →ₐ[F] L) < Module.finrank F K := by
  rcases hinsep with ⟨i, hi⟩
  refine lt_of_le_of_ne (card_algHom_le_finrank F K L) ?_
  intro hEq
  have hKsep : Algebra.IsSeparable F K := by
    rw [← Field.finSepDegree_eq_of_isAlgClosed F K L] at hEq
    exact (Field.finSepDegree_eq_finrank_iff F K).1 hEq
  have hsep_i : IsSeparable (adjoinStage F α i.castSucc) (α i) := by
    exact IsSeparable.tower_top (L := adjoinStage F α i.castSucc)
      (Algebra.IsSeparable.isSeparable F (α i))
  exact hi hsep_i

end

end FieldExtension
