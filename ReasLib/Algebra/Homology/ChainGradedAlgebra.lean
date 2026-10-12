/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Chain-graded algebras

This file owns unital associative algebras presented as an external family of
`R`-modules indexed homologically by `ℤ`.  It also provides the reusable module
of homogeneous linear-map families, including degree transport, composition,
and graded commutation.
-/

@[expose] public section

universe u v

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- A unital associative chain-graded algebra presented by its
homogeneous `R`-modules and degreewise multiplication. -/
@[stacks 09PR "infrastructure: chain-graded algebras"]
structure ChainGradedAlgebra (R : Type u) [CommRing R] where
  /-- The homogeneous component in degree `i`. -/
  X : ℤ → ModuleCat.{v} R
  /-- Multiplication of homogeneous elements. -/
  mul (i j : ℤ) : X i →ₗ[R] X j →ₗ[R] X (i + j)
  /-- The multiplicative unit in degree zero. -/
  one : X 0
  /-- Multiplication of homogeneous elements is associative. -/
  mul_assoc (i j k : ℤ) (a : X i) (b : X j) (c : X k) :
    cast (congrArg (fun n : ℤ ↦ (X n : Type v)) (add_assoc i j k))
        (mul (i + j) k (mul i j a b) c) =
      mul i (j + k) a (mul j k b c)
  /-- The degree-zero unit acts on the left. -/
  one_mul (i : ℤ) (a : X i) :
    cast (congrArg (fun n : ℤ ↦ (X n : Type v)) (zero_add i))
      (mul 0 i one a) = a
  /-- The degree-zero unit acts on the right. -/
  mul_one (i : ℤ) (a : X i) :
    cast (congrArg (fun n : ℤ ↦ (X n : Type v)) (add_zero i))
      (mul i 0 a one) = a

namespace ChainGradedAlgebra

variable (A : ChainGradedAlgebra.{u, v} R)

/-- The graded object underlying a chain-graded algebra. -/
def toGradedObject : GradedObject ℤ (ModuleCat.{v} R) :=
  A.X

/-- Evaluating the underlying graded object returns the corresponding homogeneous component. -/
@[simp]
theorem toGradedObject_apply (i : ℤ) : A.toGradedObject i = A.X i := sorry

/-- Transport between equal degrees as an `R`-linear map. -/
def reindex {i j : ℤ} (h : i = j) : A.X i →ₗ[R] A.X j :=
  ((eqToHom (congrArg A.X h) : A.X i ⟶ A.X j)).hom

/-- Degree transport acts by the corresponding cast on homogeneous elements. -/
@[simp]
theorem reindex_apply {i j : ℤ} (h : i = j) (x : A.X i) :
    A.reindex h x = cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) x := sorry

/-- A degree-`k` homogeneous linear endomorphism is an explicit
family `A.X i →ₗ[R] A.X (i + k)`. -/
@[stacks 09PR "infrastructure: homogeneous linear maps on chain-graded algebras"]
abbrev HomogeneousMap (k : ℤ) :=
  ∀ i : ℤ, A.X i →ₗ[R] A.X (i + k)

namespace HomogeneousMap

variable {A : ChainGradedAlgebra.{u, v} R} {k l m : ℤ}

/-- Two homogeneous maps are equal when they agree on every homogeneous element. -/
@[ext]
theorem ext {f g : HomogeneousMap A k}
    (h : ∀ i : ℤ, ∀ x : A.X i, f i x = g i x) : f = g := sorry

/-- Transport the degree of a homogeneous map along an equality of degrees. -/
def castDegree (h : k = l) (f : HomogeneousMap A k) : HomogeneousMap A l :=
  fun i ↦ (A.reindex (congrArg (fun n : ℤ ↦ i + n) h)).comp (f i)

/-- Degree transport is pointwise transport on the codomain. -/
@[simp]
theorem castDegree_apply (h : k = l) (f : HomogeneousMap A k)
    (i : ℤ) (x : A.X i) :
    castDegree h f i x = A.reindex (congrArg (fun n : ℤ ↦ i + n) h) (f i x) := sorry

/-- The zero homogeneous map is pointwise zero. -/
@[simp]
theorem zero_apply (i : ℤ) (x : A.X i) :
    (0 : HomogeneousMap A k) i x = 0 := sorry

/-- Addition of homogeneous maps is pointwise addition. -/
@[simp]
theorem add_apply (f g : HomogeneousMap A k) (i : ℤ) (x : A.X i) :
    (f + g) i x = f i x + g i x := sorry

/-- Scalar multiplication of homogeneous maps is pointwise scalar multiplication. -/
@[simp]
theorem smul_apply (r : R) (f : HomogeneousMap A k) (i : ℤ) (x : A.X i) :
    (r • f) i x = r • f i x := sorry

/-- Composition of homogeneous maps adds their degrees. -/
def comp (g : HomogeneousMap A l) (f : HomogeneousMap A k) :
    HomogeneousMap A (k + l) :=
  fun i ↦ (A.reindex (add_assoc i k l)).comp ((g (i + k)).comp (f i))

/-- Homogeneous composition is pointwise composition followed by degree reassociation. -/
@[simp]
theorem comp_apply (g : HomogeneousMap A l) (f : HomogeneousMap A k)
    (i : ℤ) (x : A.X i) :
    comp g f i x = A.reindex (add_assoc i k l) (g (i + k) (f i x)) := sorry

/-- Two homogeneous maps graded-commute when exchanging them produces the Koszul sign. -/
def GradedCommutes (f : HomogeneousMap A k) (g : HomogeneousMap A l) : Prop :=
  comp g f = (k * l).negOnePow • castDegree (add_comm l k) (comp f g)

/-- Two homogeneous maps commute when their two composites agree after degree transport. -/
def Commutes (f : HomogeneousMap A k) (g : HomogeneousMap A l) : Prop :=
  comp g f = castDegree (add_comm l k) (comp f g)

/-- If the product of the degrees is even, graded commutation is ordinary commutation. -/
theorem gradedCommutes_iff_commutes_of_even (f : HomogeneousMap A k)
    (g : HomogeneousMap A l) (h : Even (k * l)) :
    GradedCommutes f g ↔ Commutes f g := sorry

end HomogeneousMap

end ChainGradedAlgebra
