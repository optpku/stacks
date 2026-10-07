module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.EssentialFiniteness

public section

universe u v

namespace Algebra

/-- A finitely generated field extension has a finite-dimensional subspace whose powers
grow at least polynomially with exponent its transcendence degree. -/
theorem exists_submodule_pow_rank_growth
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    ∃ V : Submodule k K, FiniteDimensional k V ∧
      ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (n ^ Cardinal.toNat (trdeg k K) : Cardinal) ≤ C * Module.rank k (V ^ n : Submodule k K) := sorry

/-- Every finite-dimensional subspace of an essentially finite type field extension has
polynomially bounded powers, with exponent its transcendence degree. -/
theorem submodule_pow_rank_le
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (V : Submodule k K) [FiniteDimensional k V] :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Module.rank k (V ^ n : Submodule k K) ≤ (C * n ^ Cardinal.toNat (trdeg k K) : Cardinal) := sorry

/-- The natural transcendence degree is the supremum of exponents realized by
polynomial lower bounds for powers of finite-dimensional subspaces. -/
theorem trdeg_toNat_eq_sSup_pow_growth
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    Cardinal.toNat (trdeg k K) =
      sSup {e : ℕ | ∃ V : Submodule k K, FiniteDimensional k V ∧
        ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
          (n ^ e : Cardinal) ≤ C * Module.rank k (V ^ n : Submodule k K)} := sorry

/-- The natural transcendence degree is the infimum of exponents uniformly bounding
powers of every finite-dimensional subspace. -/
theorem trdeg_toNat_eq_sInf_pow_growth
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    Cardinal.toNat (trdeg k K) =
      sInf {e : ℕ | ∀ V : Submodule k K, FiniteDimensional k V →
        ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
          Module.rank k (V ^ n : Submodule k K) ≤ (C * n ^ e : Cardinal)} := sorry

end Algebra
