/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.Determinant
import StacksCheckRecall

/-!
# Determinants of two-term complexes

Lemma 15.85.12 states that the determinant of a square presentation matrix annihilates the
corresponding two-term object in the derived category.

@stack 0G9L
-/

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 15.85.12 (0G9L): if `K ∈ D(R)` is represented by a two-term complex
`Rⁿ → Rⁿ` with matrix `A`, then `det A : K ⟶ K` is zero. -/

@[stacks 0G9L "Lemma 15.85.12"]
#check fun {R : Type u} [CommRing R] {n : ℕ}
    (K : DerivedCategory (ModuleCat R)) (A : Matrix (Fin n) (Fin n) R)
    (hK : IsIsomorphic
      (DerivedCategory.Q.obj
        (CategoryTheory.DerivedCategory.TwoTermDeterminant.matrixCone A)) K) =>
  (CategoryTheory.DerivedCategory.TwoTermDeterminant.matrix_det_smul_id_eq_zero K A hK :
    Matrix.det A • 𝟙 K = 0)

@[stacks 0G9L "finite-free endomorphism companion"]
#check fun {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (K : DerivedCategory (ModuleCat R)) (f : M →ₗ[R] M)
    (hK : IsIsomorphic
      (DerivedCategory.Q.obj
        (CategoryTheory.DerivedCategory.TwoTermDeterminant.endomorphismCone f)) K) =>
  (CategoryTheory.DerivedCategory.TwoTermDeterminant.endomorphism_det_smul_id_eq_zero K f hK :
    LinearMap.det f • 𝟙 K = 0)

@[stacks 0G9L "two-term matrix presentation"]
#check fun {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) =>
  (CategoryTheory.DerivedCategory.TwoTermDeterminant.matrixCone A :
    CochainComplex (ModuleCat R) ℤ)
