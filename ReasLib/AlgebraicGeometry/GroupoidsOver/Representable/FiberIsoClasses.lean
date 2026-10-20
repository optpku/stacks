/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.GroupoidTarget
public import ReasLib.CategoryTheory.Fibered.InSetoids.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable

/-!
# Maps of setoid fibrations representable by algebraic spaces

A 1-morphism of categories fibred in setoids over `(Sch/S)_fppf` is representable
by algebraic spaces if and only if the induced map of fiberwise isomorphism-class
presheaves is, using their associated discrete groupoid fibrations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver
open Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A morphism between categories fibred in setoids is relatively representable
by algebraic spaces if and only if the morphism of discrete groupoid fibrations
associated to its canonical map on fiberwise isomorphism classes is relatively
representable by algebraic spaces. -/
@[stacks 04SY]
theorem relativelyRepresentableByAlgebraicSpaces.iff_fiberIsoClassMap
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [Functor.IsFibered.InSetoids X.p] [Functor.IsFibered.InSetoids Y.p]
    (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces
        ((Sets.toGroupoids (Over S)).map
          ((Sets.ofPresheaf (Over S)).map
            (BasedFunctor.fiberIsoClassMap (toBasedFunctor f)))) ↔
      relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- For compatible small presheaf presentations of the fiberwise isomorphism
classes of two setoid fibrations, the presented map is representable by
algebraic spaces if and only if the original morphism is relatively
representable by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces.iff_fiberIsoClass_ulift
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [Functor.IsFibered.InSetoids X.p] [Functor.IsFibered.InSetoids Y.p]
    (f : X ⟶ Y) {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (iX : Functor.fiberIsoClassPresheaf X.p ≅ F ⋙ uliftFunctor.{u + 1, u})
    (iY : Functor.fiberIsoClassPresheaf Y.p ≅ G ⋙ uliftFunctor.{u + 1, u})
    (ha : BasedFunctor.fiberIsoClassMap (toBasedFunctor f) =
      iX.hom ≫ Functor.whiskerRight a uliftFunctor.{u + 1, u} ≫ iY.inv) :
    AlgebraicSpace.representableByAlgebraicSpaces a ↔
      relativelyRepresentableByAlgebraicSpaces f :=
  sorry

end AlgebraicGeometry
