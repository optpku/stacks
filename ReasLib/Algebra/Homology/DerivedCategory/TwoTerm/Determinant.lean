/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.LinearAlgebra.Determinant
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinants of two-term derived modules

This file owns the mapping-cone presentations of two-term derived modules and the
determinant-annihilation statements for square matrices and finite free endomorphisms.

@stack 0G9L
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.DerivedCategory.TwoTermDeterminant

section

variable {R : Type u} [CommRing R]

local notation "DMod" => _root_.DerivedCategory (ModuleCat R)
local notation "single₀" => CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)

/-- The canonical two-term cochain complex attached to an endomorphism `f`, represented as
the mapping cone of the induced map between degree-zero single complexes. -/
@[stacks 0G9L "two-term endomorphism cone"]
noncomputable abbrev endomorphismCone {M : Type v} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] M) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.mappingCone ((single₀).map (ModuleCat.ofHom f))

/-- The canonical two-term cochain complex attached to a square matrix `A`. -/
@[stacks 0G9L "two-term matrix cone"]
noncomputable abbrev matrixCone {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) : CochainComplex (ModuleCat R) ℤ :=
  endomorphismCone A.toLin'

/-- Lemma 15.85.12: if `K` is represented by the two-term complex
`Rⁿ → Rⁿ` with differential matrix `A`, then multiplication by `det A` is zero on
`K` in `D(R)`. -/
@[stacks 0G9L "Lemma 15.85.12"]
theorem matrix_det_smul_id_eq_zero {n : ℕ}
    (K : DMod) (A : Matrix (Fin n) (Fin n) R)
    (hK : IsIsomorphic (_root_.DerivedCategory.Q.obj (matrixCone A)) K) :
    Matrix.det A • 𝟙 K = 0 := sorry
/- Proof strategy: use the adjugate identities `A ⬝ adjugate A = det A • 1` and
`adjugate A ⬝ A = det A • 1` to construct a null-homotopy of scalar multiplication by
`Matrix.det A` on `matrixCone A`; apply `DerivedCategory.Q` and transport the vanishing across
the isomorphism `hK`. -/

/-- The finite-free endomorphism form of determinant annihilation for a two-term derived
module. -/
@[stacks 0G9L "finite-free endomorphism form"]
theorem endomorphism_det_smul_id_eq_zero
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (K : DMod) (f : M →ₗ[R] M)
    (hK : IsIsomorphic (_root_.DerivedCategory.Q.obj (endomorphismCone f)) K) :
    LinearMap.det f • 𝟙 K = 0 := sorry
/- Proof strategy: choose a finite basis of the finite free module `M`, identify `f` and its cone
with the corresponding matrix presentation, apply `matrix_det_smul_id_eq_zero`, and transport
along the basis-induced cone isomorphism using invariance of `LinearMap.det`. -/

end

end CategoryTheory.DerivedCategory.TwoTermDeterminant
