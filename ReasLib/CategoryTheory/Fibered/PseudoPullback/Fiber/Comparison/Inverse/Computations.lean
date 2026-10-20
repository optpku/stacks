/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Comparison.Inverse.Construction

/-!
# Computations for the inverse fibre comparison

This leaf exposes how the canonical inverse comparison reconstructs the base, the two projections,
the stored comparison isomorphism, and morphism components.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback

universe u v uX uY uS vX vY vS

namespace CategoryTheory
namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

noncomputable section

namespace PseudoPullback
namespace Fiber

/-- The inverse comparison constructs its total object over the specified base object. -/
@[simp] theorem comparisonInverse.obj.base
    {U : C} (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    PseudoPullback.baseObj
        (Functor.Fiber.fiberInclusion.obj ((comparisonInverse F G U).obj P)) =
      U := sorry

/-- The inverse comparison preserves the first object component. -/
@[simp] theorem comparisonInverse.obj.fst
    {U : C} (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    PseudoPullback.fstObj
        (Functor.Fiber.fiberInclusion.obj ((comparisonInverse F G U).obj P)) =
      P.fst.1 := sorry

/-- The inverse comparison preserves the second object component. -/
@[simp] theorem comparisonInverse.obj.snd
    {U : C} (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    PseudoPullback.sndObj
        (Functor.Fiber.fiberInclusion.obj ((comparisonInverse F G U).obj P)) =
      P.snd.1 := sorry

/-- The inverse comparison preserves the object comparison morphism. -/
@[simp] theorem comparisonInverse.obj.comparisonHom
    {U : C} (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    PseudoPullback.comparison
        (Functor.Fiber.fiberInclusion.obj ((comparisonInverse F G U).obj P)) =
      P.iso.hom.1 := sorry

/-- The full comparison isomorphism of a fibre-pullback object is the ambient image of its
stored fibrewise comparison isomorphism. -/
@[simp]
theorem comparisonInverse.obj.comparisonIso
    {U : C} (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    PseudoPullback.comparisonIsoApp
        (Functor.Fiber.fiberInclusion.obj ((comparisonInverse F G U).obj P)) =
      Functor.Fiber.fiberInclusion.mapIso P.iso := sorry

/-- The inverse comparison preserves the first morphism component. -/
@[simp] theorem comparisonInverse.map.fst
    {U : C} {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)} (φ : P ⟶ Q) :
    PseudoPullback.fstMap
        (Functor.Fiber.fiberInclusion.map ((comparisonInverse F G U).map φ)) =
      φ.fst.1 := sorry

/-- The inverse comparison preserves the second morphism component. -/
@[simp] theorem comparisonInverse.map.snd
    {U : C} {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)} (φ : P ⟶ Q) :
    PseudoPullback.sndMap
        (Functor.Fiber.fiberInclusion.map ((comparisonInverse F G U).map φ)) =
      φ.snd.1 := sorry

/-- The total morphism constructed by the inverse comparison is vertical over the specified
base object. -/
@[simp] theorem comparisonInverse.map.base
    {U : C} {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)} (φ : P ⟶ Q) :
    PseudoPullback.baseMap
        (Functor.Fiber.fiberInclusion.map ((comparisonInverse F G U).map φ)) =
      𝟙 U := sorry

end Fiber
end PseudoPullback
end

end BasedCategory
end CategoryTheory
