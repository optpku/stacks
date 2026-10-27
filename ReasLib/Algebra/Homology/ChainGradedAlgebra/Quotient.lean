/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Predifferential
public import ReasLib.LinearAlgebra.BilinearMap
public import ReasLib.LinearAlgebra.QuotientByIdeal.QuotientRing
public import ReasLib.LinearAlgebra.QuotientByIdeal.Scalar
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotients of chain-graded algebras by base ideals

The degreewise quotient of an `R`-graded algebra by the multiples of `I : Ideal R` is naturally a
graded algebra over `R ⧸ I`.  Multiplication is constructed by scalar-extending the source
bilinear maps and transporting them through the canonical tensor-quotient equivalences.  Thus its
computational data does not depend on a choice of representatives or a deferred well-definedness
proof.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v

variable {R : Type u} [CommRing R]

namespace ChainGradedAlgebra

namespace IdealQuotient

variable (A : ChainGradedAlgebra.{u, v} R) (I : Ideal R)

/-- The degree-`i` component of a chain-graded algebra modulo the multiples of `I`. -/
@[stacks 00DV "homogeneous component modulo a base ideal"]
abbrev Piece (i : ℤ) : Type v :=
  A.X i ⧸ (I • (⊤ : Submodule R (A.X i)))

/-- The canonical scalar-extension identification with the degreewise quotient by `I`. -/
@[stacks 00DV "tensor description of a homogeneous ideal quotient"]
def tensorEquiv (i : ℤ) :
    ((R ⧸ I) ⊗[R] A.X i) ≃ₗ[R ⧸ I] Piece A I i :=
  Ideal.Quotient.tensorModuleEquiv I (A.X i)

/-- The quotient map onto the degree-`i` component, viewed as an `R`-linear map. -/
def mk (i : ℤ) : A.X i →ₗ[R] Piece A I i :=
  (tensorEquiv A I i).toLinearMap.restrictScalars R ∘ₗ
    TensorProduct.mk R (R ⧸ I) (A.X i) 1

/-- The tensor description sends a pure tensor with coefficient one to the quotient class. -/
@[simp]
theorem tensorEquiv_one_tmul (i : ℤ) (x : A.X i) :
    tensorEquiv A I i (1 ⊗ₜ[R] x) = mk A I i x := rfl

/-- The tensor construction of the quotient map is the usual quotient class map. -/
theorem mk_eq_mk (i : ℤ) (x : A.X i) :
    mk A I i x = Submodule.Quotient.mk x :=
  Ideal.Quotient.tensorModuleEquiv_one_tmul I (A.X i) x

/-- Every homogeneous quotient element has a representative. -/
theorem mk_surjective (i : ℤ) : Function.Surjective (mk A I i) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨x, mk_eq_mk A I i x⟩

private theorem cast_mk {i j : ℤ} (h : i = j) (x : A.X i) :
    cast (congrArg (fun n : ℤ ↦ Piece A I n) h) (mk A I i x) =
      mk A I j (cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) x) := by
  subst j
  rfl

/-- The scalar extension of homogeneous multiplication to `R ⧸ I`. -/
def tensorMul (i j : ℤ) :
    ((R ⧸ I) ⊗[R] A.X i) →ₗ[R ⧸ I]
      ((R ⧸ I) ⊗[R] A.X j) →ₗ[R ⧸ I]
        ((R ⧸ I) ⊗[R] A.X (i + j)) :=
  (A.mul i j).baseChange₂

/-- Homogeneous multiplication on the degreewise quotient by `I`. -/
@[stacks 00DV "homogeneous multiplication modulo a base ideal"]
def mul (i j : ℤ) :
    Piece A I i →ₗ[R ⧸ I] Piece A I j →ₗ[R ⧸ I] Piece A I (i + j) :=
  ((tensorMul A I i j).compl₁₂
      (tensorEquiv A I i).symm.toLinearMap
      (tensorEquiv A I j).symm.toLinearMap).compr₂
    (tensorEquiv A I (i + j)).toLinearMap

/-- Quotient multiplication sends representatives to the class of their product. -/
@[simp]
theorem mul_mk (i j : ℤ) (x : A.X i) (y : A.X j) :
    mul A I i j (mk A I i x) (mk A I j y) =
      mk A I (i + j) (A.mul i j x y) := by
  change tensorEquiv A I (i + j)
      (tensorMul A I i j
        ((tensorEquiv A I i).symm (tensorEquiv A I i (1 ⊗ₜ[R] x)))
        ((tensorEquiv A I j).symm (tensorEquiv A I j (1 ⊗ₜ[R] y)))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  simp only [tensorMul, LinearMap.baseChange₂,
    TensorProduct.AlgebraTensorModule.lift_tmul, LinearMap.toSpanSingleton_apply_one,
    LinearMap.comp_apply, LinearMap.baseChangeHom_apply, LinearMap.baseChange_tmul]
  rfl

/-- The quotient class of the source unit. -/
def one : Piece A I 0 :=
  mk A I 0 A.one

/-- Multiplication on the quotient is associative. -/
theorem mul_assoc (i j k : ℤ) (x : Piece A I i) (y : Piece A I j)
    (z : Piece A I k) :
    cast (congrArg (fun n : ℤ ↦ Piece A I n) (add_assoc i j k))
        (mul A I (i + j) k (mul A I i j x y) z) =
      mul A I i (j + k) x (mul A I j k y z) := by
  obtain ⟨x, rfl⟩ := mk_surjective A I i x
  obtain ⟨y, rfl⟩ := mk_surjective A I j y
  obtain ⟨z, rfl⟩ := mk_surjective A I k z
  rw [mul_mk, mul_mk, mul_mk, mul_mk, cast_mk A I (add_assoc i j k), A.mul_assoc]

/-- The quotient class of the source unit acts on the left. -/
theorem one_mul (i : ℤ) (x : Piece A I i) :
    cast (congrArg (fun n : ℤ ↦ Piece A I n) (zero_add i))
        (mul A I 0 i (one A I) x) = x := by
  obtain ⟨x, rfl⟩ := mk_surjective A I i x
  rw [one, mul_mk, cast_mk A I (zero_add i), A.one_mul]

/-- The quotient class of the source unit acts on the right. -/
theorem mul_one (i : ℤ) (x : Piece A I i) :
    cast (congrArg (fun n : ℤ ↦ Piece A I n) (add_zero i))
        (mul A I i 0 x (one A I)) = x := by
  obtain ⟨x, rfl⟩ := mk_surjective A I i x
  rw [one, mul_mk, cast_mk A I (add_zero i), A.mul_one]

end IdealQuotient

/-- The chain-graded algebra over `R ⧸ I` obtained by quotienting every homogeneous component by
the multiples of `I`. -/
@[stacks 00DV "chain-graded algebra modulo a base ideal"]
def quotientByIdeal (A : ChainGradedAlgebra.{u, v} R) (I : Ideal R) :
    ChainGradedAlgebra.{u, v} (R ⧸ I) where
  X i := ModuleCat.of (R ⧸ I) (IdealQuotient.Piece A I i)
  mul := IdealQuotient.mul A I
  one := IdealQuotient.one A I
  mul_assoc := IdealQuotient.mul_assoc A I
  one_mul := IdealQuotient.one_mul A I
  mul_one := IdealQuotient.mul_one A I

namespace IdealQuotient

/-- Quotient classes commute with transport between equal homogeneous degrees. -/
theorem reindex_mk (A : ChainGradedAlgebra.{u, v} R) (I : Ideal R)
    {i j : ℤ} (h : i = j) (x : A.X i) :
    (A.quotientByIdeal I).reindex h (mk A I i x) = mk A I j (A.reindex h x) := by
  subst j
  rfl

end IdealQuotient

namespace HomogeneousMap

variable {A : ChainGradedAlgebra.{u, v} R} {k : ℤ}

/-- A homogeneous endomorphism induces a homogeneous endomorphism after quotienting every
component by the same base ideal. -/
@[stacks 00DV "homogeneous maps modulo a base ideal"]
def quotientByIdeal (D : HomogeneousMap A k) (I : Ideal R) :
    HomogeneousMap (A.quotientByIdeal I) k :=
  fun i ↦ LinearMap.IdealQuotient.map (D i) I

/-- The quotient of a homogeneous map sends the class of a representative to the class of its
image. -/
@[simp]
theorem quotientByIdeal_mk (D : HomogeneousMap A k) (I : Ideal R)
    (i : ℤ) (x : A.X i) :
    D.quotientByIdeal I i (IdealQuotient.mk A I i x) =
      IdealQuotient.mk A I (i + k) (D i x) := by
  rw [IdealQuotient.mk_eq_mk, IdealQuotient.mk_eq_mk]
  exact LinearMap.IdealQuotient.map_mk (D i) I x

end HomogeneousMap

namespace Derivation

variable {A : ChainGradedAlgebra.{u, v} R} {k : ℤ}

/-- The componentwise quotient of a graded derivation satisfies the graded Leibniz rule. -/
theorem quotientByIdeal_mem (D : Derivation A k) (I : Ideal R) :
    HomogeneousMap.quotientByIdeal (toHomogeneousMap D) I ∈
      derivationSubmodule (A.quotientByIdeal I) k := by
  change SatisfiesLeibniz (A.quotientByIdeal I) k _
  intro i j x y
  obtain ⟨x, rfl⟩ := IdealQuotient.mk_surjective A I i x
  obtain ⟨y, rfl⟩ := IdealQuotient.mk_surjective A I j y
  change HomogeneousMap.quotientByIdeal (toHomogeneousMap D) I (i + j)
      (IdealQuotient.mul A I i j (IdealQuotient.mk A I i x) (IdealQuotient.mk A I j y)) =
    (A.quotientByIdeal I).reindex (add_right_comm i k j)
        (IdealQuotient.mul A I (i + k) j
          (HomogeneousMap.quotientByIdeal (toHomogeneousMap D) I i
            (IdealQuotient.mk A I i x)) (IdealQuotient.mk A I j y)) +
      (k * i).negOnePow •
        (A.quotientByIdeal I).reindex (add_assoc i j k).symm
          (IdealQuotient.mul A I i (j + k) (IdealQuotient.mk A I i x)
            (HomogeneousMap.quotientByIdeal (toHomogeneousMap D) I j
              (IdealQuotient.mk A I j y)))
  rw [IdealQuotient.mul_mk, HomogeneousMap.quotientByIdeal_mk,
    HomogeneousMap.quotientByIdeal_mk, HomogeneousMap.quotientByIdeal_mk,
    IdealQuotient.mul_mk, IdealQuotient.mul_mk,
    IdealQuotient.reindex_mk A I (add_right_comm i k j),
    IdealQuotient.reindex_mk A I (add_assoc i j k).symm]
  have h := congrArg (IdealQuotient.mk A I (i + j + k)) (D.property i j x y)
  rw [map_add] at h
  refine h.trans ?_
  congr 1
  change IdealQuotient.mk A I (i + j + k)
      (((k * i).negOnePow : ℤ) • _) =
    ((k * i).negOnePow : ℤ) • IdealQuotient.mk A I (i + j + k) _
  exact map_zsmul (IdealQuotient.mk A I (i + j + k)) _ _

/-- A graded derivation descends canonically through the quotient by a base ideal. -/
@[stacks 00DV "graded derivations modulo a base ideal"]
def quotientByIdeal (D : Derivation A k) (I : Ideal R) :
    Derivation (A.quotientByIdeal I) k :=
  ⟨HomogeneousMap.quotientByIdeal (toHomogeneousMap D) I,
    quotientByIdeal_mem D I⟩

/-- The descended derivation sends the class of a representative to the class of its image. -/
@[simp]
theorem quotientByIdeal_mk (D : Derivation A k) (I : Ideal R)
    (i : ℤ) (x : A.X i) :
    Derivation.quotientByIdeal D I i (IdealQuotient.mk A I i x) =
      IdealQuotient.mk A I (i + k) (D i x) :=
  HomogeneousMap.quotientByIdeal_mk (toHomogeneousMap D) I i x

end Derivation

namespace Predifferential

variable {A : ChainGradedAlgebra.{u, v} R}

/-- A predifferential descends canonically through the quotient by a base ideal. -/
abbrev quotientByIdeal (d : Predifferential A) (I : Ideal R) :
    Predifferential (A.quotientByIdeal I) :=
  Derivation.quotientByIdeal d I

/-- Quotienting the square derivation agrees with squaring the quotient predifferential. -/
theorem square_quotientByIdeal (d : Predifferential A) (I : Ideal R) :
    Derivation.quotientByIdeal (square d) I =
      square (Predifferential.quotientByIdeal d I) := by
  apply Subtype.ext
  funext i
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := IdealQuotient.mk_surjective A I i x
  change HomogeneousMap.quotientByIdeal (squareMap d) I i (IdealQuotient.mk A I i x) =
    (A.quotientByIdeal I).reindex (add_assoc i (-1) (-1))
      (Derivation.quotientByIdeal d I (i + -1)
        (Derivation.quotientByIdeal d I i (IdealQuotient.mk A I i x)))
  rw [HomogeneousMap.quotientByIdeal_mk, Derivation.quotientByIdeal_mk,
    Derivation.quotientByIdeal_mk, IdealQuotient.reindex_mk]
  rfl

/-- A square-zero predifferential remains square-zero after quotienting by a base ideal. -/
theorem isSquareZero_quotientByIdeal {d : Predifferential A}
    (hd : IsSquareZero d) (I : Ideal R) :
    IsSquareZero (Predifferential.quotientByIdeal d I) := by
  change squareMap (Predifferential.quotientByIdeal d I) = 0
  funext i
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := IdealQuotient.mk_surjective A I i x
  change (A.quotientByIdeal I).reindex (add_assoc i (-1) (-1))
      (Derivation.quotientByIdeal d I (i + -1)
        (Derivation.quotientByIdeal d I i (IdealQuotient.mk A I i x))) = 0
  rw [Derivation.quotientByIdeal_mk, Derivation.quotientByIdeal_mk,
    IdealQuotient.reindex_mk]
  change IdealQuotient.mk A I (i + -2) (squareMap d i x) = 0
  have hx : squareMap d i x = 0 :=
    congrArg (fun f : HomogeneousMap A (-2) ↦ f i x) hd
  rw [hx, map_zero]

end Predifferential

end ChainGradedAlgebra
