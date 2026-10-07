module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Opposite
public import ReasLib.Algebra.Homology.CochainDGAlgebra.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Enveloping Differential Graded Algebras

The enveloping DGA of a pair `(A, B)` is the Koszul tensor product `A.opposite ⊗[R] B`.
This leaf also owns the two canonical factor maps used to restrict an enveloping module to its
left and right module structures.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open ComplexShape HomologicalComplex
open scoped TensorProduct

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- Lemma 22.28.3 (0FQJ): the enveloping DGA governing differential graded `(A, B)`-bimodules
is the Koszul tensor product `A.opposite ⊗[R] B`. -/
@[reducible, stacks 0FQJ "enveloping differential graded algebra"]
def enveloping (A : CochainDGAlgebra.{u, v} R) (B : CochainDGAlgebra.{u, w} R) :
    CochainDGAlgebra.{u, max v w} R :=
  tensorProduct A.opposite B

namespace Enveloping

variable (A : CochainDGAlgebra.{u, v} R) (B : CochainDGAlgebra.{u, w} R)

/-- The total degree of the left-factor summand `A.opposite.X i ⊗ B.X 0` is `i`. -/
theorem leftDegree (i : ℤ) :
    (up ℤ).π (up ℤ) (up ℤ) (i, 0) = i := sorry

/-- The total degree of the right-factor summand `A.opposite.X 0 ⊗ B.X j` is `j`. -/
theorem rightDegree (j : ℤ) :
    (up ℤ).π (up ℤ) (up ℤ) (0, j) = j := sorry

/-- A homogeneous pure tensor in the enveloping DGA. -/
def pure {i j : ℤ} (a : A.opposite.X i) (b : B.X j) :
    (enveloping A B).X (i + j) :=
  (CochainDGAlgebra.Tensor.summandInclusion A.opposite B
    i j (i + j) (Tensor.totalDegree i j)).hom (a ⊗ₜ[R] b)

/-- Include a homogeneous element of `A.opposite` into the left factor of the enveloping DGA. -/
def left {i : ℤ} (a : A.opposite.X i) : (enveloping A B).X i :=
  (CochainDGAlgebra.Tensor.summandInclusion A.opposite B
    i 0 i (leftDegree i)).hom (a ⊗ₜ[R] B.one)

/-- Include a homogeneous element of `B` into the right factor of the enveloping DGA. -/
def right {j : ℤ} (b : B.X j) : (enveloping A B).X j :=
  (CochainDGAlgebra.Tensor.summandInclusion A.opposite B
    0 j j (rightDegree j)).hom (A.one ⊗ₜ[R] b)

/-- The homogeneous left-factor inclusion as a linear map. -/
def leftLinearMap (i : ℤ) : A.opposite.X i →ₗ[R] (enveloping A B).X i where
  toFun := left A B
  map_add' := sorry
  map_smul' := sorry

/-- The homogeneous right-factor inclusion as a linear map. -/
def rightLinearMap (j : ℤ) : B.X j →ₗ[R] (enveloping A B).X j where
  toFun := right A B
  map_add' := sorry
  map_smul' := sorry

/-- The canonical DGA homomorphism from `A.opposite` to the enveloping DGA. -/
@[stacks 0FQJ "left factor of the enveloping differential graded algebra"]
def leftHom : Hom A.opposite (enveloping A B) where
  map := leftLinearMap A B
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- The canonical DGA homomorphism from `B` to the enveloping DGA. -/
@[stacks 0FQJ "right factor of the enveloping differential graded algebra"]
def rightHom : Hom B (enveloping A B) where
  map := rightLinearMap A B
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- The left factor homomorphism acts by tensoring with the unit of `B`. -/
@[simp]
theorem leftHom_apply (i : ℤ) (a : A.opposite.X i) :
    leftHom A B i a = left A B a := sorry

/-- The right factor homomorphism acts by tensoring with the unit of `A.opposite`. -/
@[simp]
theorem rightHom_apply (j : ℤ) (b : B.X j) :
    rightHom A B j b = right A B b := sorry

end Enveloping

end CochainDGAlgebra
