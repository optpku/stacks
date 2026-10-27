/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Representable

/-!
# Structure morphism of the stack of relatively perfect complexes

The structure morphism records the scheme over the base supporting an
admissible complex, using its Yoneda element in the groupoid fibration of the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The projection from admissible complexes on fibres of `f` to their test
schemes over `B`. -/
def toSchemesOver (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    category f ⥤ SchemeOver B where
  obj x := x.σ
  map α := α.base
  map_id := sorry
  map_comp := sorry

/-- The object part of `toSchemesOver` is the test scheme of a complex. -/
theorem toSchemesOver_obj (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    (x : category f) :
    (toSchemesOver f).obj x = x.σ := sorry

/-- The morphism part of `toSchemesOver` is the underlying map of schemes over `B`. -/
theorem toSchemesOver_map {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {x y : category f} (α : x ⟶ y) :
    (toSchemesOver f).map α = α.base := sorry

/-- Forgetting the structure map to `B` recovers the projection to `Over S`. -/
theorem toSchemesOver_comp_proj (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] :
    toSchemesOver f ⋙ CostructuredArrow.proj (ofOverFunctor S) B = p f := sorry

/-- The structure functor sends an admissible complex over `g : T ⟶ B` to the
universe-lifted opposite category-of-elements point of `g`. -/
def toBaseFunctor (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    category f ⥤ ULiftHom.{u + 1} B.functorOfPoints.Elementsᵒᵖ where
  obj x := ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩)
  map {x y} α := ULiftHom.up.map (Quiver.Hom.op (CategoryOfElements.homMk
    ⟨op y.σ.left, yonedaEquiv y.σ.hom⟩ ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩
    α.base.left.op sorry))
  map_id := sorry
  map_comp := sorry

/-- Objectwise, the structure functor is the lifted opposite Yoneda element
of the structure map of the test scheme. -/
theorem toBaseFunctor_obj (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    (x : category f) :
    (toBaseFunctor f).obj x =
      ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩) := sorry

/-- The structure functor lies strictly over `Over S`. -/
theorem toBaseFunctor_p (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    toBaseFunctor f ⋙ Classifying.toGroupoidsProjection B = p f := sorry

/-- The structure 1-morphism of the groupoid fibration of admissible complexes
forgets the complex and records its test scheme over `B`. -/
def toBase (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    toGroupoids f ⟶ Classifying.toGroupoids B :=
  ofBasedFunctor (BasedFunctor.ofFunctor (toBaseFunctor f) (toBaseFunctor_p f))

/-- The total functor of the structure 1-morphism is the structure functor. -/
theorem toBase_toFunctor (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    toFunctor (toBase f) = toBaseFunctor f := sorry

/-- The structure 1-morphism lies strictly over `Over S`. -/
theorem toBase_p (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    toFunctor (toBase f) ⋙ (Classifying.toGroupoids B).p = p f := sorry

/-- On objects, the structure 1-morphism is the lifted opposite Yoneda element
of the structure map of the test scheme. -/
theorem toBase_obj (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    (x : category f) :
    (toFunctor (toBase f)).obj x =
      ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩) := sorry

/-- The projection of the structure 1-morphism records the underlying scheme
of the projection to schemes over `B`. -/
theorem toBase_spec (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    (x : category f) :
    (Classifying.toGroupoidsProjection B).obj ((toFunctor (toBase f)).obj x) =
      ((toSchemesOver f).obj x).left := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
