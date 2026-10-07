module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap99.Lemma_99_5_2
public import stacks_project.Chap110.Lemma_110_53_1

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

/-- The underlying functor of the structure morphism `CohStack f ⟶ B`, sending
an object `(T, g, F)` to the universe-lifted opposite category-of-elements
point of `g : T ⟶ B`. -/
def forgetFunctor (f : X ⟶ B) [FinitePresentation f] :
    Obj f ⥤ ULiftHom.{u + 1} B.functorOfPoints.Elementsᵒᵖ where
  obj x :=
    ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩)
  map {x y} α :=
    ⟨Quiver.Hom.op
      (CategoryOfElements.homMk
        ⟨op y.σ.left, yonedaEquiv y.σ.hom⟩
        ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩
        α.base.left.op sorry)⟩
  map_id := sorry
  map_comp := sorry

/-- Objectwise, `forgetFunctor` is the universe-lifted opposite element of the
structure morphism `g : T ⟶ B`. -/
theorem forgetFunctor_obj (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    (forgetFunctor f).obj x =
      ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩) :=
  sorry

/-- `forgetFunctor` lies strictly over `Over S`. -/
theorem forgetFunctor_p (f : X ⟶ B) [FinitePresentation f] :
    forgetFunctor f ⋙ Classifying.toGroupoidsProjection B = p f :=
  sorry

/-- The structure 1-morphism `CohStack f ⟶ B` of groupoid fibrations over
`Over S`. -/
def forget (f : X ⟶ B) [FinitePresentation f] :
    toGroupoids f ⟶ Classifying.toGroupoids B :=
  ofBasedFunctor (BasedFunctor.ofFunctor (forgetFunctor f) (forgetFunctor_p f))

/-- Forgetting `forget` to based functors recovers `BasedFunctor.ofFunctor` of
`forgetFunctor`. -/
theorem forget.toBasedFunctor (f : X ⟶ B) [FinitePresentation f] :
    FiberedCategoryOver.Groupoids.toBasedFunctor (forget f) =
      BasedFunctor.ofFunctor (forgetFunctor f) (forgetFunctor_p f) :=
  sorry

/-- The structure morphism lies strictly over `Over S`. -/
theorem forget_p (f : X ⟶ B) [FinitePresentation f] :
    FiberedCategoryOver.Groupoids.toFunctor (forget f) ⋙
        Classifying.toGroupoidsProjection B =
      p f :=
  sorry

/-- On objects, `forget` sends `(T, g, F)` to the functor-of-points element of
`g`. -/
theorem forget_obj (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    (FiberedCategoryOver.Groupoids.toFunctor (forget f)).obj x =
      ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
