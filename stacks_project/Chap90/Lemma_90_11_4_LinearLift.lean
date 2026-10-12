/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Types.Products
public import stacks_project.Chap90.Definition_90_11_1_ModuleLinear

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

universe u v w

namespace CategoryTheory.Functor

variable {C : Type w} [Category.{v} C] [Preadditive C] [HasBinaryProducts C]

/-- The sum map `M ⨯ M ⟶ M` sending a pair to the sum of its projections. -/
def sumHom (M : C) : M ⨯ M ⟶ M :=
  prod.fst + prod.snd

/-- The sum map is the sum of the binary product projections. -/
theorem sumHom_eq (M : C) : sumHom M = prod.fst + prod.snd := sorry

variable {R : Type u} [CommRing R]
variable [CategoryTheory.Linear R C] [HasFiniteProducts C] [HasZeroObject C]
variable (L : C ⥤ Type v) [PreservesFiniteProducts L] [Unique (L.obj 0)]

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

/-- The additive group structure on `L.obj M`. -/
instance instAddCommGroup (M : C) : AddCommGroup (L.obj M) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- The `R`-module structure on `L.obj M`. -/
instance instModule (M : C) : Module R (L.obj M) where
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The unique `R`-linear lift of `L` through the forgetful functor `ModuleCat R ⥤ Type`. -/
def linearLift : C ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (L.obj M)
  map f := ModuleCat.ofHom
    { toFun := fun x ↦ L.map f x
      map_add' := sorry
      map_smul' := sorry }
  map_id := sorry
  map_comp := sorry

/-- The lifted functor has object `ModuleCat.of R (L.obj M)` at `M`. -/
theorem linearLift_obj (M : C) :
    (linearLift L).obj M = ModuleCat.of R (L.obj M) := sorry

/-- The lifted functor acts on morphisms by the underlying map of `L`. -/
theorem linearLift_map {M N : C} (f : M ⟶ N) (x : L.obj M) :
    (linearLift L : C ⥤ ModuleCat.{v} R).map f x = L.map f x := sorry

/-- The lift composes with the forgetful functor to recover `L`. -/
theorem linearLift_comp_forget :
    linearLift L ⋙ forget (ModuleCat.{v} R) = L := sorry

/-- The lift is an additive functor. -/
instance instAdditive : (linearLift L : C ⥤ ModuleCat.{v} R).Additive := sorry

/-- The lift is an `R`-linear functor. -/
instance instLinear : Linear R (linearLift L : C ⥤ ModuleCat.{v} R) := sorry

/-- The lift is module-linear over `R`. -/
instance instModuleLinear : ModuleLinear R (linearLift L : C ⥤ ModuleCat.{v} R) := sorry

/-- A module-linear functor over `L` is equal to `linearLift L`. -/
theorem linearLift_unique (G : C ⥤ ModuleCat.{v} R) [ModuleLinear R G]
    (hG : G ⋙ forget (ModuleCat.{v} R) = L) :
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
