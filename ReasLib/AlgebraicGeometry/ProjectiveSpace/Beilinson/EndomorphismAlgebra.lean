module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.Generator
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Linear
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology.Naturality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Biproduct
public import Mathlib.Algebra.Algebra.Subalgebra.Matrix
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The Beilinson endomorphism algebra of projective space

This module presents the endomorphisms of the standard finite sum of negative twists on
projective space as matrices whose entries have the prescribed homogeneous degrees.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Beilinson

variable (A : Type u) [CommRing A] (n : ℕ)

/-- Homogeneous degree conditions are closed under matrix multiplication. -/
theorem matrixAlgebra_mul_mem
    (M N : Matrix (Fin (n + 1)) (Fin (n + 1))
      (MvPolynomial (Fin (n + 1)) A))
    (hM : ∀ i j : Fin (n + 1), M i j ∈ gradedPiece A n ((j : ℤ) - (i : ℤ)))
    (hN : ∀ i j : Fin (n + 1), N i j ∈ gradedPiece A n ((j : ℤ) - (i : ℤ))) :
    ∀ i j : Fin (n + 1), (M * N) i j ∈ gradedPiece A n ((j : ℤ) - (i : ℤ)) := sorry

/-- Homogeneous degree conditions are closed under matrix addition. -/
theorem matrixAlgebra_add_mem
    (M N : Matrix (Fin (n + 1)) (Fin (n + 1))
      (MvPolynomial (Fin (n + 1)) A))
    (hM : ∀ i j : Fin (n + 1), M i j ∈ gradedPiece A n ((j : ℤ) - (i : ℤ)))
    (hN : ∀ i j : Fin (n + 1), N i j ∈ gradedPiece A n ((j : ℤ) - (i : ℤ))) :
    ∀ i j : Fin (n + 1), (M + N) i j ∈ gradedPiece A n ((j : ℤ) - (i : ℤ)) := sorry

/-- Scalar matrices satisfy the homogeneous degree conditions. -/
theorem matrixAlgebra_algebraMap_mem (a : A) :
    ∀ i j : Fin (n + 1), (algebraMap A
      (Matrix (Fin (n + 1)) (Fin (n + 1))
        (MvPolynomial (Fin (n + 1)) A)) a) i j ∈
      gradedPiece A n ((j : ℤ) - (i : ℤ)) := sorry

/-- The matrix algebra whose row-`i`, column-`j` entry is homogeneous of degree `j - i`. -/
def matrixAlgebra :
    Subalgebra A (Matrix (Fin (n + 1)) (Fin (n + 1))
      (MvPolynomial (Fin (n + 1)) A)) where
  carrier := {M | ∀ i j : Fin (n + 1),
    M i j ∈ gradedPiece A n ((j : ℤ) - (i : ℤ))}
  mul_mem' := fun {M N} hM hN ↦ matrixAlgebra_mul_mem A n M N hM hN
  add_mem' := fun {M N} hM hN ↦ matrixAlgebra_add_mem A n M N hM hN
  algebraMap_mem' := fun a ↦ matrixAlgebra_algebraMap_mem A n a

/-- The degree condition defining `matrixAlgebra`. -/
theorem mem_matrixAlgebra
    (M : Matrix (Fin (n + 1)) (Fin (n + 1))
      (MvPolynomial (Fin (n + 1)) A)) :
    M ∈ matrixAlgebra A n ↔
      ∀ i j : Fin (n + 1),
        M i j ∈ gradedPiece A n ((j : ℤ) - (i : ℤ)) := sorry

/-- An entry on or above the diagonal belongs to its natural homogeneous component. -/
theorem upperEntry_mem_grading (M : matrixAlgebra A n) (i j : Fin (n + 1))
    (h : i ≤ j) :
    M.1 i j ∈ grading A n ((j : ℕ) - (i : ℕ)) := sorry

/-- An entry strictly below the diagonal vanishes. -/
theorem lowerEntry_eq_zero (M : matrixAlgebra A n) (i j : Fin (n + 1))
    (h : j < i) :
    M.1 i j = 0 := sorry

/-- An upper-triangular graded entry can be read in its natural homogeneous degree. -/
theorem entry_mem_grading (i j : Fin (n + 1)) (h : i ≤ j)
    (f : gradedPiece A n ((j : ℤ) - (i : ℤ))) :
    f.1 ∈ grading A n ((j : ℕ) - (i : ℕ)) := sorry

/-- The target twist of upper-triangular homogeneous multiplication is the row twist. -/
theorem entryTwistingSheaf_eq (i j : Fin (n + 1)) (h : i ≤ j) :
    twistingSheaf A n
        (-(j : ℤ) + (((j : ℕ) - (i : ℕ) : ℕ) : ℤ)) =
      twistingSheaf A n (-(i : ℤ)) := sorry

/-- The explicit morphism represented by one graded matrix entry. -/
noncomputable def entryMap (i j : Fin (n + 1))
    (f : gradedPiece A n ((j : ℤ) - (i : ℤ))) :
    twistingSheaf A n (-(j : ℤ)) ⟶ twistingSheaf A n (-(i : ℤ)) :=
  if h : i ≤ j then
    twistingSheaf.mulHomogeneous n (-(j : ℤ)) ((j : ℕ) - (i : ℕ))
        f.1 (entry_mem_grading A n i j h f) ≫
      eqToHom (entryTwistingSheaf_eq A n i j h)
  else
    0

/-- Entrywise homogeneous multiplication preserves addition. -/
theorem entryMap_add (i j : Fin (n + 1))
    (f g : gradedPiece A n ((j : ℤ) - (i : ℤ))) :
    entryMap A n i j (f + g) = entryMap A n i j f + entryMap A n i j g := sorry

/-- Entrywise homogeneous multiplication respects the base-ring scalar action. -/
theorem entryMap_smul (i j : Fin (n + 1)) (a : A)
    (f : gradedPiece A n ((j : ℤ) - (i : ℤ))) :
    entryMap A n i j (a • f) = a • entryMap A n i j f := sorry

/-- A homogeneous matrix entry acts by multiplication between the corresponding twists. -/
noncomputable def entryHom (i j : Fin (n + 1)) :
    gradedPiece A n ((j : ℤ) - (i : ℤ)) →ₗ[A]
      (twistingSheaf A n (-(j : ℤ)) ⟶ twistingSheaf A n (-(i : ℤ))) where
  toFun := entryMap A n i j
  map_add' := entryMap_add A n i j
  map_smul' := entryMap_smul A n i j

/-- The entry map is homogeneous multiplication above the diagonal and zero below it. -/
theorem entryHom_apply (i j : Fin (n + 1))
    (f : gradedPiece A n ((j : ℤ) - (i : ℤ))) :
    entryHom A n i j f =
      if h : i ≤ j then
        twistingSheaf.mulHomogeneous n (-(j : ℤ)) ((j : ℕ) - (i : ℕ))
            f.1 (entry_mem_grading A n i j h f) ≫
          eqToHom (entryTwistingSheaf_eq A n i j h)
      else
        0 := sorry

/-- Homogeneous polynomials identify each graded entry with the corresponding twist morphisms. -/
theorem entryHom_bijective (i j : Fin (n + 1)) :
    Function.Bijective (entryHom A n i j) := sorry

/-- The underlying endomorphism represented by a graded matrix. -/
noncomputable def toEndFun (M : matrixAlgebra A n) :
    End (beilinsonGenerator A n) :=
  (biproduct.isoCoproduct
      (fun i : Fin (n + 1) ↦ twistingSheaf A n (-(i : ℤ)))).inv ≫
    biproduct.matrix (fun j i ↦
      entryHom A n i j
        ⟨M.1 i j, (mem_matrixAlgebra A n M.1).mp M.2 i j⟩) ≫
    (biproduct.isoCoproduct
      (fun i : Fin (n + 1) ↦ twistingSheaf A n (-(i : ℤ)))).hom

/-- The graded-matrix comparison preserves one. -/
theorem toEndFun_one :
    toEndFun A n 1 = 1 := sorry

/-- The graded-matrix comparison preserves multiplication. -/
theorem toEndFun_mul (M N : matrixAlgebra A n) :
    toEndFun A n (M * N) = toEndFun A n M * toEndFun A n N := sorry

/-- The graded-matrix comparison preserves zero. -/
theorem toEndFun_zero :
    toEndFun A n 0 = 0 := sorry

/-- The graded-matrix comparison preserves addition. -/
theorem toEndFun_add (M N : matrixAlgebra A n) :
    toEndFun A n (M + N) = toEndFun A n M + toEndFun A n N := sorry

/-- Scalar matrices act as scalar endomorphisms of the Beilinson generator. -/
theorem toEndFun_algebraMap (a : A) :
    toEndFun A n (algebraMap A (matrixAlgebra A n) a) =
      algebraMap A (End (beilinsonGenerator A n)) a := sorry

/-- The concrete algebra map from graded matrices to endomorphisms of the Beilinson generator. -/
noncomputable def toEnd :
    matrixAlgebra A n →ₐ[A] End (beilinsonGenerator A n) where
  toFun := toEndFun A n
  map_one' := toEndFun_one A n
  map_mul' := toEndFun_mul A n
  map_zero' := toEndFun_zero A n
  map_add' := toEndFun_add A n
  commutes' := toEndFun_algebraMap A n

/-- The `(j,i)` biproduct component of the represented endomorphism is the action of the
row-`i`, column-`j` matrix entry. -/
theorem toEnd_apply (M : matrixAlgebra A n) (j i : Fin (n + 1)) :
    biproduct.components
        ((biproduct.isoCoproduct
            (fun k : Fin (n + 1) ↦ twistingSheaf A n (-(k : ℤ)))).hom ≫
          toEnd A n M ≫
          (biproduct.isoCoproduct
            (fun k : Fin (n + 1) ↦ twistingSheaf A n (-(k : ℤ)))).inv)
        j i =
      entryHom A n i j
        ⟨M.1 i j, (mem_matrixAlgebra A n M.1).mp M.2 i j⟩ := sorry

/-- The graded-matrix comparison is a bijection onto the endomorphism algebra. -/
theorem toEnd_bijective :
    Function.Bijective (toEnd A n) := sorry

end AlgebraicGeometry.ProjectiveSpace.Beilinson

end
