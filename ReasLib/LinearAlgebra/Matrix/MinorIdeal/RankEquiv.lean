module

public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Operations
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Rank

/-!
# Coordinate Equivalence Invariance of Rank Minor Ideals

This leaf records the invariance of the exterior rank and its associated
rank-minor ideal under changes of finite free coordinates.

@stack 00N1
-/

@[expose] public section

universe u

namespace LinearMap

variable {R : Type u} [CommRing R]

/-- Composing a coordinate linear map with source and target linear automorphisms
does not change its exterior rank. -/
@[stacks 00N1 "exterior rank under coordinate equivalence"]
theorem exteriorRank_comp_equiv_eq {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    exteriorRank (eTarget.toLinearMap.comp (φ.comp eSource.toLinearMap)) = exteriorRank φ := sorry

/-- Composing a coordinate linear map with source and target linear automorphisms
does not change its rank-minor ideal. -/
@[stacks 00N1 "rank-minor ideal under coordinate equivalence"]
theorem rankMinorIdeal_comp_equiv_eq {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    rankMinorIdeal (eTarget.toLinearMap.comp (φ.comp eSource.toLinearMap)) =
      rankMinorIdeal φ := sorry

/-- A coordinate linear equivalence between possibly differently written finite free
modules preserves exterior rank.  `InvariantBasisNumber R` identifies the displayed
source and target ranks. -/
@[stacks 00N1 "exterior rank under finite free coordinate equivalence"]
theorem exteriorRank_eq_of_equiv [InvariantBasisNumber R] {m n m' n' : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m' → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n' → R)) :
    exteriorRank (eTarget.toLinearMap.comp (φ.comp eSource.toLinearMap)) = exteriorRank φ := sorry

/-- A coordinate linear equivalence between possibly differently written finite free
modules preserves the rank-minor ideal.  `InvariantBasisNumber R` identifies the
displayed source and target ranks. -/
@[stacks 00N1 "rank-minor ideal under finite free coordinate equivalence"]
theorem rankMinorIdeal_eq_of_equiv [InvariantBasisNumber R] {m n m' n' : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (eSource : (Fin m' → R) ≃ₗ[R] (Fin m → R))
    (eTarget : (Fin n → R) ≃ₗ[R] (Fin n' → R)) :
    rankMinorIdeal (eTarget.toLinearMap.comp (φ.comp eSource.toLinearMap)) =
      rankMinorIdeal φ := sorry

end LinearMap
