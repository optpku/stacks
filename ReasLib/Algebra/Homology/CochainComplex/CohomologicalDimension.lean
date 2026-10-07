module

public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty
public import ReasLib.CategoryTheory.Abelian.CohomologicalDimension
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomological Dimension and Unbounded Cochain Complexes

This file owns the complex-level convergence condition and dimension-lowering replacement
theorems associated with a cohomological-dimension function.  The categorical axioms on the
function itself live in `ReasLib.CategoryTheory.Abelian.CohomologicalDimension`.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.ShiftedDimension

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The shifted dimensions of `K` tend to `-∞` in negative degrees when every integer bound
eventually bounds `n + d (K.X n)`.  The natural-number witness also records that the relevant
values of `d` are finite. -/
@[stacks 07K6]
def TendstoNegInf (K : CochainComplex A ℤ) (d : A → WithTop ℕ) : Prop :=
  ∀ N : ℤ, ∃ n₀ : ℤ, ∀ n ≤ n₀,
    ∃ m : ℕ, d (K.X n) = m ∧ n + m ≤ N

namespace TendstoNegInf

variable {d : A → WithTop ℕ} {K L : CochainComplex A ℤ}

/-- The quantified bound characterizing shifted-dimension convergence. -/
theorem iff : TendstoNegInf K d ↔
    ∀ N : ℤ, ∃ n₀ : ℤ, ∀ n ≤ n₀,
      ∃ m : ℕ, d (K.X n) = m ∧ n + m ≤ N := sorry

/-- Sufficiently far in negative degrees, a complex with shifted dimension tending to `-∞`
has finite dimension values. -/
theorem eventuallyFinite (hK : TendstoNegInf K d) (N : ℤ) :
    ∃ n₀ : ℤ, ∀ n ≤ n₀, ∃ m : ℕ, d (K.X n) = m := sorry

/-- Shifted-dimension convergence is invariant under isomorphisms of complexes when `d` is a
cohomological-dimension function. -/
theorem iffOfIso [CategoryTheory.CohomologicalDimension.IsFunction d] (e : K ≅ L) :
    TendstoNegInf K d ↔ TendstoNegInf L d := sorry

/-- 07K6 (Lemma 13.32.1): a complex whose shifted dimensions tend to `-∞` admits a
quasi-isomorphic replacement in the termwise zero locus of `d`. -/
@[stacks 07K6]
theorem existsQuasiIso [CategoryTheory.CohomologicalDimension.IsFunction d]
    (hK : TendstoNegInf K d) :
    ∃ (L : CochainComplex A ℤ) (α : K ⟶ L),
      QuasiIso α ∧
        CochainComplex.termsIn
          (CategoryTheory.CohomologicalDimension.zeroLocus d) L := sorry

/-- The numerical view of `existsQuasiIso`, exposing zero dimension of every replacement term. -/
theorem existsQuasiIso_zero [CategoryTheory.CohomologicalDimension.IsFunction d]
    (hK : TendstoNegInf K d) :
    ∃ (L : CochainComplex A ℤ) (α : K ⟶ L),
      QuasiIso α ∧ ∀ n : ℤ, d (L.X n) = 0 := sorry

end TendstoNegInf

end CochainComplex.ShiftedDimension
