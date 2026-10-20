/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.FiberIsoClasses
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver
open Groupoids
open scoped Bicategory

noncomputable section

universe u

/- Lemma 94.9.6: let `S` be an object of `Sch_fppf`. Let `f : X ⟶ Y` be a
1-morphism of categories fibred in setoids over `(Sch/S)_fppf`. Let `F` and `G`
be the presheaves `Functor.fiberIsoClassPresheaf X.p` and
`Functor.fiberIsoClassPresheaf Y.p` of fiberwise isomorphism classes, and let
`a` be the map of presheaves `BasedFunctor.fiberIsoClassMap (toBasedFunctor f)`
corresponding to `f`. Then `a` is representable by algebraic spaces in the
sense of Bootstrap Definition 80.3.1, encoded via Lemma 94.9.5 as relative
representability of the associated map of categories fibred in sets, if and only
if `f` is representable by algebraic spaces. -/
@[stacks 04SY]
#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.iff_fiberIsoClassMap :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [Functor.IsFibered.InSetoids X.p] [Functor.IsFibered.InSetoids Y.p]
    (f : X ⟶ Y),
    relativelyRepresentableByAlgebraicSpaces
        ((Sets.toGroupoids (Over S)).map
          ((Sets.ofPresheaf (Over S)).map
            (BasedFunctor.fiberIsoClassMap (toBasedFunctor f)))) ↔
      relativelyRepresentableByAlgebraicSpaces f)

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.iff_fiberIsoClass_ulift :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [Functor.IsFibered.InSetoids X.p] [Functor.IsFibered.InSetoids Y.p]
    (f : X ⟶ Y) {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (iX : Functor.fiberIsoClassPresheaf X.p ≅ F ⋙ uliftFunctor.{u + 1, u})
    (iY : Functor.fiberIsoClassPresheaf Y.p ≅ G ⋙ uliftFunctor.{u + 1, u})
    (ha : BasedFunctor.fiberIsoClassMap (toBasedFunctor f) =
      iX.hom ≫ Functor.whiskerRight a uliftFunctor.{u + 1, u} ≫ iY.inv),
    AlgebraicSpace.representableByAlgebraicSpaces a ↔
      relativelyRepresentableByAlgebraicSpaces f)
