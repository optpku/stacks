/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Representable

/-!
# Structure morphism of the stack of coherent sheaves

A finite-presentation morphism `f : X ⟶ B` of algebraic spaces determines a
1-morphism `forget f : toGroupoids f ⟶ Classifying.toGroupoids B` over
`Over S`, sending `(T, g, F)` to the functor-of-points element of `g`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme Opposite
open CategoryTheory.BasedFunctor
open CategoryTheory.FiberedCategoryOver.Groupoids
open scoped CategoryTheory.BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

section StructureFunctor

-- The exposed functor is assembled from private concrete map data and law proofs.
set_option backward.privateInPublic true

/-- A morphism of coherent sheaves respects the corresponding functor-of-points elements. -/
private theorem forgetMap_w (f : X ⟶ B) [FinitePresentation f] {x y : Obj f}
    (α : x ⟶ y) :
    B.functorOfPoints.map α.base.left.op (yonedaEquiv y.σ.hom) =
      yonedaEquiv x.σ.hom := sorry

/-- The morphism on opposite elements induced by the base map of a coherent-sheaf morphism. -/
private def forgetMap (f : X ⟶ B) [FinitePresentation f] {x y : Obj f}
    (α : x ⟶ y) :
    ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩) ⟶
      (ULiftHom.objUp (op ⟨op y.σ.left, yonedaEquiv y.σ.hom⟩) :
        ULiftHom.{u + 1} B.functorOfPoints.Elementsᵒᵖ) :=
  ⟨Quiver.Hom.op (CategoryOfElements.homMk
    ⟨op y.σ.left, yonedaEquiv y.σ.hom⟩ ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩
    α.base.left.op (forgetMap_w f α))⟩

/-- The map on opposite elements preserves identity morphisms. -/
private theorem forgetMap_id (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    forgetMap f (𝟙 x) = 𝟙 _ := sorry

/-- The map on opposite elements preserves composition. -/
private theorem forgetMap_comp (f : X ⟶ B) [FinitePresentation f]
    {x y z : Obj f} (α : x ⟶ y) (β : y ⟶ z) :
    forgetMap f (α ≫ β) = forgetMap f α ≫ forgetMap f β := sorry

/-- The structure functor sends a coherent sheaf over `g : T ⟶ B` to the
universe-lifted opposite category-of-elements point of `g`. -/
def forgetFunctor (f : X ⟶ B) [FinitePresentation f] :
    Obj f ⥤ ULiftHom.{u + 1} B.functorOfPoints.Elementsᵒᵖ where
  obj x := ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩)
  map α := forgetMap f α
  map_id := forgetMap_id f
  map_comp := forgetMap_comp f

end StructureFunctor

/-- Objectwise, `forgetFunctor` is the universe-lifted opposite element of the
structure morphism `g : T ⟶ B`. -/
theorem forgetFunctor_obj (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    (forgetFunctor f).obj x =
      ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩) := sorry

/-- `forgetFunctor` lies strictly over `Over S`. -/
theorem forgetFunctor_p (f : X ⟶ B) [FinitePresentation f] :
    forgetFunctor f ⋙ Classifying.toGroupoidsProjection B = p f := sorry

/-- The structure 1-morphism `CohStack f ⟶ B` of groupoid fibrations over
`Over S`. -/
def forget (f : X ⟶ B) [FinitePresentation f] :
    toGroupoids f ⟶ Classifying.toGroupoids B :=
  ofBasedFunctor (BasedFunctor.ofFunctor (forgetFunctor f) (forgetFunctor_p f))

/-- Forgetting `forget` to based functors recovers `BasedFunctor.ofFunctor` of
`forgetFunctor`. -/
theorem forget.toBasedFunctor (f : X ⟶ B) [FinitePresentation f] :
    FiberedCategoryOver.Groupoids.toBasedFunctor (forget f) =
      BasedFunctor.ofFunctor (forgetFunctor f) (forgetFunctor_p f) := sorry

/-- The structure morphism lies strictly over `Over S`. -/
theorem forget_p (f : X ⟶ B) [FinitePresentation f] :
    FiberedCategoryOver.Groupoids.toFunctor (forget f) ⋙
        Classifying.toGroupoidsProjection B =
      p f := sorry

/-- On objects, `forget` sends `(T, g, F)` to the functor-of-points element of
`g`. -/
theorem forget_obj (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    (FiberedCategoryOver.Groupoids.toFunctor (forget f)).obj x =
      ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩) := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
