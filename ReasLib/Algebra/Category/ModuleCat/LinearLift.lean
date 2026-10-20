/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Types.Products
public import ReasLib.CategoryTheory.Linear.Functor
public import ReasLib.Algebra.Category.FGModuleCat.FiniteProducts

/-!
# The unique `R`-linear lift of a finite-product-preserving functor to types

A functor `L : C ⥤ Type v` from an `R`-linear category with finite products and a
zero object, with `L.obj 0` a singleton and `L` preserving finite products, lifts
uniquely to an `R`-linear functor `C ⥤ ModuleCat R` whose composite with the
forgetful functor is `L`.
-/

@[expose] public section

open CategoryTheory hiding Linear
open Limits ZeroObject

noncomputable section

universe u v w vL

namespace CategoryTheory.Functor

variable {C : Type w} [Category.{v} C] [Preadditive C] [HasBinaryProducts C]

/-- The sum map `M ⨯ M ⟶ M` sending a pair to the sum of its projections. -/
def sumHom (M : C) : M ⨯ M ⟶ M :=
  prod.fst + prod.snd

/-- The sum map is the sum of the binary product projections. -/
theorem sumHom_eq (M : C) : sumHom M = prod.fst + prod.snd := sorry

variable {R : Type u} [CommRing R]
variable [CategoryTheory.Linear R C] [HasFiniteProducts C] [HasZeroObject C]
variable (L : C ⥤ Type vL) [PreservesFiniteProducts L] [Unique (L.obj 0)]

/-- Addition on the values of a finite-product-preserving functor to types. -/
instance instAdd (M : C) : Add (L.obj M) where
  add x y :=
    L.map (sumHom M)
      ((asIso (prodComparison L M M)).inv
        ((Types.binaryProductIso (L.obj M) (L.obj M)).inv (x, y)))

/-- The zero element on the values of a finite-product-preserving functor to types. -/
instance instZero (M : C) : Zero (L.obj M) where
  zero := L.map (0 : (0 : C) ⟶ M) (default : L.obj 0)

/-- Negation on the values of a finite-product-preserving functor to types. -/
instance instNeg (M : C) : Neg (L.obj M) where
  neg x := L.map (-𝟙 M) x

/-- Scalar multiplication on the values of a finite-product-preserving functor to types. -/
instance instSMul (M : C) : SMul R (L.obj M) where
  smul r x := L.map (r • 𝟙 M) x

/-- Addition induced by the product comparison is associative. -/
theorem linearLift_add_assoc (M : C) (x y z : L.obj M) :
    x + y + z = x + (y + z) := sorry

/-- The image of the unique point at the zero object is a left additive identity. -/
theorem linearLift_zero_add (M : C) (x : L.obj M) : 0 + x = x := sorry

/-- The image of the unique point at the zero object is a right additive identity. -/
theorem linearLift_add_zero (M : C) (x : L.obj M) : x + 0 = x := sorry

/-- The image of negative identity gives additive inverses. -/
theorem linearLift_neg_add_cancel (M : C) (x : L.obj M) : -x + x = 0 := sorry

/-- Addition induced by the product comparison is commutative. -/
theorem linearLift_add_comm (M : C) (x y : L.obj M) : x + y = y + x := sorry

/-- The additive group structure on `L.obj M`. -/
instance instAddCommGroup (M : C) : AddCommGroup (L.obj M) where
  add_assoc := linearLift_add_assoc L M
  zero_add := linearLift_zero_add L M
  add_zero := linearLift_add_zero L M
  nsmul := nsmulRec
  neg_add_cancel := linearLift_neg_add_cancel L M
  zsmul := zsmulRec
  add_comm := linearLift_add_comm L M

/-- The scalar action induced by scalar identity sends `1 • x` to `x`. -/
theorem linearLift_one_smul (M : C) (x : L.obj M) : (1 : R) • x = x := sorry

/-- The scalar action induced by scalar identity respects multiplication of scalars. -/
theorem linearLift_mul_smul (M : C) (r s : R) (x : L.obj M) :
    (r * s) • x = r • (s • x) := sorry

/-- The scalar action induced by scalar identity sends zero to zero. -/
theorem linearLift_smul_zero (M : C) (r : R) : r • (0 : L.obj M) = 0 := sorry

/-- The scalar action induced by scalar identity distributes over addition of elements. -/
theorem linearLift_smul_add (M : C) (r : R) (x y : L.obj M) :
    r • (x + y) = r • x + r • y := sorry

/-- The scalar action induced by scalar identity distributes over addition of scalars. -/
theorem linearLift_add_smul (M : C) (r s : R) (x : L.obj M) :
    (r + s) • x = r • x + s • x := sorry

/-- The scalar action induced by scalar identity sends the zero scalar to zero. -/
theorem linearLift_zero_smul (M : C) (x : L.obj M) : (0 : R) • x = 0 := sorry

/-- The `R`-module structure on `L.obj M`. -/
instance instModule (M : C) : Module R (L.obj M) where
  one_smul := linearLift_one_smul L M
  mul_smul := linearLift_mul_smul L M
  smul_zero := linearLift_smul_zero L M
  smul_add := linearLift_smul_add L M
  add_smul := linearLift_add_smul L M
  zero_smul := linearLift_zero_smul L M

/-- The map of `L` on a morphism preserves the induced addition. -/
theorem linearLift_map_add {M N : C} (f : M ⟶ N) (x y : L.obj M) :
    L.map f (x + y) = L.map f x + L.map f y := sorry

/-- The map of `L` on a morphism preserves the induced scalar action. -/
theorem linearLift_map_smul {M N : C} (f : M ⟶ N) (r : R) (x : L.obj M) :
    L.map f (r • x) = r • L.map f x := sorry

/-- The linear map on the values of `L` whose underlying function is `L.map f`. -/
def linearLiftMap {M N : C} (f : M ⟶ N) : L.obj M →ₗ[R] L.obj N where
  toFun := fun x ↦ L.map f x
  map_add' := linearLift_map_add L f
  map_smul' := linearLift_map_smul L f

/-- Packaging the lifted identity map gives the identity in `ModuleCat R`. -/
theorem linearLiftMap_id (M : C) :
    ModuleCat.ofHom (linearLiftMap L (𝟙 M)) = 𝟙 (ModuleCat.of R (L.obj M)) := sorry

/-- Packaging lifted maps respects composition in `ModuleCat R`. -/
theorem linearLiftMap_comp {M N P : C} (f : M ⟶ N) (g : N ⟶ P) :
    ModuleCat.ofHom (linearLiftMap (R := R) L (f ≫ g)) =
      ModuleCat.ofHom (linearLiftMap L f) ≫ ModuleCat.ofHom (linearLiftMap L g) := sorry

/-- The unique `R`-linear lift of `L` through the forgetful functor `ModuleCat R ⥤ Type`. -/
def linearLift : C ⥤ ModuleCat.{vL} R where
  obj M := ModuleCat.of R (L.obj M)
  map f := ModuleCat.ofHom (linearLiftMap L f)
  map_id := linearLiftMap_id L
  map_comp := linearLiftMap_comp L

/-- The lifted functor has object `ModuleCat.of R (L.obj M)` at `M`. -/
theorem linearLift_obj (M : C) :
    (linearLift L).obj M = ModuleCat.of R (L.obj M) := sorry

/-- The lifted functor acts on morphisms by the underlying map of `L`. -/
theorem linearLift_map {M N : C} (f : M ⟶ N) (x : L.obj M) :
    (linearLift L : C ⥤ ModuleCat.{vL} R).map f x = L.map f x := sorry

/-- The lift composes with the forgetful functor to recover `L`. -/
theorem linearLift_comp_forget :
    linearLift L ⋙ forget (ModuleCat.{vL} R) = L := sorry

/-- The lift is an additive functor. -/
instance instAdditive : (linearLift L : C ⥤ ModuleCat.{vL} R).Additive := sorry

/-- The lift is an `R`-linear functor. -/
instance instLinear : Linear R (linearLift L : C ⥤ ModuleCat.{vL} R) := sorry

/-- The lift is module-linear over `R`. -/
instance instModuleLinear : ModuleLinear R (linearLift L : C ⥤ ModuleCat.{vL} R) :=
  ModuleLinear.ofAdditiveLinear (R := R) (linearLift L)

/-- A module-linear functor over `L` is equal to `linearLift L`. -/
theorem linearLift_unique (G : C ⥤ ModuleCat.{vL} R) [ModuleLinear R G]
    (hG : G ⋙ forget (ModuleCat.{vL} R) = L) :
    G = linearLift L := sorry

/-- Addition on the lift is induced by the sum map and the product comparison isomorphism. -/
theorem linearLift_add {M : C} (x y : L.obj M) :
    x + y =
      L.map (sumHom M)
        ((asIso (prodComparison L M M)).inv
          ((Types.binaryProductIso (L.obj M) (L.obj M)).inv (x, y))) := sorry

/-- Scalar multiplication on the lift is induced by `r • 𝟙 M`. -/
theorem linearLift_smul {M : C} (r : R) (x : L.obj M) :
    r • x = L.map (r • 𝟙 M) x := sorry

/-- The zero of the lift is the image of the unique point of `L.obj 0`. -/
theorem linearLift_zero (M : C) :
    (0 : L.obj M) = L.map (0 : (0 : C) ⟶ M) (default : L.obj 0) := sorry

end CategoryTheory.Functor

variable {R : Type u} [CommRing R]

namespace FGModuleCat

/-- A finite-product-preserving functor on finitely generated modules that sends zero
to a singleton has a unique module-linear lift with the same underlying functor. -/
theorem existsUnique_linearLift (L : FGModuleCat.{v} R ⥤ Type v)
    [PreservesFiniteProducts L] [Unique (L.obj 0)] :
    ∃! F : FGModuleCat.{v} R ⥤ ModuleCat.{v} R,
      F.ModuleLinear R ∧ F ⋙ forget (ModuleCat.{v} R) = L := sorry

end FGModuleCat

namespace ModuleCat

/-- A finite-product-preserving functor on modules that sends zero to a singleton
has a unique module-linear lift with the same underlying functor. -/
theorem existsUnique_linearLift (L : ModuleCat.{v} R ⥤ Type v)
    [PreservesFiniteProducts L] [Unique (L.obj 0)] :
    ∃! F : ModuleCat.{v} R ⥤ ModuleCat.{v} R,
      F.ModuleLinear R ∧ F ⋙ forget (ModuleCat.{v} R) = L := sorry

end ModuleCat
