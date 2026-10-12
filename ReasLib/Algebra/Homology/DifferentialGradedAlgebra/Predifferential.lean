/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Hom
public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Predifferential
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Category

/-!
# Chain differential graded algebras as graded algebras with a predifferential

This file is the canonical bridge from the existing chain-DGA presentation to
the reusable chain-graded algebra, predifferential, and graded-homomorphism API.
-/

@[expose] public section

universe u v

open CategoryTheory

variable {R : Type u} [CommRing R]

namespace ChainDGAlgebra

/-- The chain-graded algebra underlying a chain differential graded algebra. -/
@[stacks 09PR "infrastructure: the chain-graded algebra underlying a chain DGA"]
def toChainGradedAlgebra (A : ChainDGAlgebra.{u, v} R) : ChainGradedAlgebra.{u, v} R where
  X := A.X
  mul := A.mul
  one := A.one
  mul_assoc := A.mul_assoc
  one_mul := A.one_mul
  mul_one := A.mul_one

/-- The homogeneous components of the underlying chain-graded algebra are the DGA components. -/
@[simp]
theorem toChainGradedAlgebra_X (A : ChainDGAlgebra.{u, v} R) (i : ℤ) :
    A.toChainGradedAlgebra.X i = A.X i := sorry

/-- Multiplication in the underlying chain-graded algebra is the DGA multiplication. -/
@[simp]
theorem toChainGradedAlgebra_mul (A : ChainDGAlgebra.{u, v} R) (i j : ℤ) :
    A.toChainGradedAlgebra.mul i j = A.mul i j := sorry

/-- The unit of the underlying chain-graded algebra is the DGA unit. -/
@[simp]
theorem toChainGradedAlgebra_one (A : ChainDGAlgebra.{u, v} R) :
    A.toChainGradedAlgebra.one = A.one := sorry

/-- The explicit degree-`-1` homogeneous map family underlying the DGA differential. -/
def predifferentialMap (A : ChainDGAlgebra.{u, v} R) :
    ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra (-1) :=
  fun i ↦ (A.d i).hom

/-- The differential family acts by the original chain-complex differential. -/
@[simp]
theorem predifferentialMap_apply (A : ChainDGAlgebra.{u, v} R) (i : ℤ) (x : A.X i) :
    predifferentialMap A i x = A.d i x := sorry

/-- The DGA Leibniz rule makes its differential family a degree-`-1` derivation. -/
theorem predifferentialMap_mem (A : ChainDGAlgebra.{u, v} R) :
    predifferentialMap A ∈
      ChainGradedAlgebra.derivationSubmodule A.toChainGradedAlgebra (-1) := sorry

/-- The canonical predifferential of a chain differential graded algebra. -/
@[stacks 09PR "infrastructure: the predifferential of a chain DGA"]
def predifferential (A : ChainDGAlgebra.{u, v} R) :
    ChainGradedAlgebra.Predifferential A.toChainGradedAlgebra :=
  ⟨predifferentialMap A, predifferentialMap_mem A⟩

/-- The homogeneous map underlying the canonical predifferential is the differential family. -/
@[simp]
theorem predifferential_toHomogeneousMap (A : ChainDGAlgebra.{u, v} R) :
    ChainGradedAlgebra.Derivation.toHomogeneousMap A.predifferential =
      predifferentialMap A := sorry

/-- The canonical predifferential acts by the original DGA differential. -/
@[simp]
theorem predifferential_apply (A : ChainDGAlgebra.{u, v} R) (i : ℤ) (x : A.X i) :
    A.predifferential i x = A.d i x := sorry

/-- The original DGA Leibniz rule in the reusable predifferential indexing convention. -/
theorem predifferential_leibniz_apply (A : ChainDGAlgebra.{u, v} R) (i j : ℤ)
    (a : A.X i) (b : A.X j) :
    A.predifferential (i + j) (A.mul i j a b) =
      A.toChainGradedAlgebra.reindex (add_right_comm i (-1) j)
          (A.mul (i - 1) j (A.d i a) b) +
        i.negOnePow •
          A.toChainGradedAlgebra.reindex (add_assoc i j (-1)).symm
            (A.mul i (j - 1) a (A.d j b)) := sorry

/-- Applying the square map is applying the original DGA differential twice. -/
theorem predifferential_squareMap_apply (A : ChainDGAlgebra.{u, v} R)
    (i : ℤ) (x : A.X i) :
    ChainGradedAlgebra.Predifferential.squareMap A.predifferential i x =
      A.toChainGradedAlgebra.reindex (add_assoc i (-1) (-1))
        (A.d (i - 1) (A.d i x)) := sorry

/-- The canonical predifferential of a chain DGA is square-zero. -/
theorem predifferential_isSquareZero (A : ChainDGAlgebra.{u, v} R) :
    ChainGradedAlgebra.Predifferential.IsSquareZero A.predifferential := sorry

end ChainDGAlgebra

namespace ChainDGAlgebra.Hom

variable {A B C : ChainDGAlgebra.{u, v} R}

/-- The explicit degreewise linear family underlying a chain-DGA homomorphism. -/
def componentMap (f : A ⟶ B) :
    ∀ i : ℤ, A.toChainGradedAlgebra.X i →ₗ[R] B.toChainGradedAlgebra.X i :=
  fun i ↦ ((f : Hom A B).toChainMap.f i).hom

/-- The component family of a chain-DGA homomorphism preserves the unit. -/
theorem componentMap_one (f : A ⟶ B) :
    componentMap f 0 A.toChainGradedAlgebra.one = B.toChainGradedAlgebra.one := sorry

/-- The component family of a chain-DGA homomorphism preserves homogeneous multiplication. -/
theorem componentMap_mul (f : A ⟶ B) (i j : ℤ)
    (a : A.toChainGradedAlgebra.X i) (b : A.toChainGradedAlgebra.X j) :
    componentMap f (i + j) (A.toChainGradedAlgebra.mul i j a b) =
      B.toChainGradedAlgebra.mul i j (componentMap f i a) (componentMap f j b) := sorry

/-- Forget differential compatibility from a chain-DGA homomorphism. -/
@[stacks 09PR "infrastructure: the underlying graded homomorphism of a chain-DGA map"]
def toGradedHom (f : A ⟶ B) :
    A.toChainGradedAlgebra ⟶ B.toChainGradedAlgebra where
  map := componentMap f
  map_one := componentMap_one f
  map_mul := componentMap_mul f

/-- The degreewise linear map of `toGradedHom f` is the original chain-map component. -/
@[simp]
theorem toGradedHom_map (f : A ⟶ B) (i : ℤ) :
    (toGradedHom f : ChainGradedAlgebra.Hom
      A.toChainGradedAlgebra B.toChainGradedAlgebra).map i =
        ((f : Hom A B).toChainMap.f i).hom := sorry

/-- The underlying graded homomorphism acts degreewise as the chain-DGA homomorphism. -/
@[simp]
theorem toGradedHom_apply (f : A ⟶ B) (i : ℤ) (x : A.X i) :
    toGradedHom f i x = f i x := sorry

/-- Passing to the underlying graded homomorphism preserves identities. -/
@[simp]
theorem toGradedHom_id (A : ChainDGAlgebra.{u, v} R) :
    toGradedHom (𝟙 A) = 𝟙 A.toChainGradedAlgebra := sorry

/-- Passing to the underlying graded homomorphism preserves composition. -/
@[simp]
theorem toGradedHom_comp (f : A ⟶ B) (g : B ⟶ C) :
    toGradedHom (f ≫ g) = toGradedHom f ≫ toGradedHom g := sorry

/-- The underlying graded homomorphism intertwines the canonical predifferentials. -/
@[simp]
theorem toGradedHom_map_predifferential_apply (f : A ⟶ B)
    (i : ℤ) (x : A.X i) :
    toGradedHom f (i - 1) (A.predifferential i x) =
      B.predifferential i (toGradedHom f i x) := sorry

end ChainDGAlgebra.Hom

namespace ChainDGAlgebra

/-- Forget a chain DGA to its underlying chain-graded algebra. -/
@[stacks 09PR "infrastructure: the underlying chain-graded algebra functor of chain DGAs"]
def toChainGraded (R : Type u) [CommRing R] :
    ChainDGAlgebra.{u, v} R ⥤ ChainGradedAlgebra.{u, v} R where
  obj A := A.toChainGradedAlgebra
  map f := Hom.toGradedHom f
  map_id A := Hom.toGradedHom_id A
  map_comp f g := Hom.toGradedHom_comp f g

/-- The underlying chain-graded algebra functor has the canonical object map. -/
@[simp]
theorem toChainGraded_obj (A : ChainDGAlgebra.{u, v} R) :
    (toChainGraded R).obj A = A.toChainGradedAlgebra := sorry

/-- The underlying chain-graded algebra functor has the canonical morphism map. -/
@[simp]
theorem toChainGraded_map {A B : ChainDGAlgebra.{u, v} R} (f : A ⟶ B) :
    (toChainGraded R).map f = Hom.toGradedHom f := sorry

end ChainDGAlgebra
