/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}}

/-- The identity morphism of a module-valued functor. -/
def Hom.id (F : ModuleValuedFunctor.{u, v} A) : Hom F F where
  app := fun _ ↦ 𝟙 _
  naturality := sorry

/-- The composite of morphisms of module-valued functors. -/
def Hom.comp {F G H : ModuleValuedFunctor.{u, v} A} (f : Hom F G) (g : Hom G H) : Hom F H where
  app := fun B ↦ f.app B ≫ g.app B
  naturality := sorry

/-- The category structure on module-valued functors whose morphisms have linear components
over every algebra. -/
@[reducible]
def category : Category (ModuleValuedFunctor.{u, v} A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The category of module-valued functors with linear component morphisms. -/
def bundled (A : CommRingCat.{u}) : Cat :=
  @Cat.of (ModuleValuedFunctor.{u, v} A) category

/-- The category of module-valued functors has componentwise zero morphisms. -/
@[reducible]
def bundledHasZeroMorphisms (A : CommRingCat.{u}) :
    HasZeroMorphisms (bundled.{u, v} A) where
  zero F G :=
    { zero :=
        { app := fun _ ↦ 0
          naturality := sorry } }
  comp_zero := sorry
  zero_comp := sorry

/-- The category of module-valued functors admits kernels. -/
theorem bundledHasKernels (A : CommRingCat.{u}) :
    @HasKernels (bundled.{u, v} A) _ (bundledHasZeroMorphisms.{u, v} A) := sorry

/-- A module-valued functor is injective for the explicit category structure on
module-valued functors. -/
abbrev IsInjective (I : ModuleValuedFunctor.{u, v} A) : Prop :=
  @CategoryTheory.Injective (ModuleValuedFunctor.{u, v} A) category I

end ModuleValuedFunctor
