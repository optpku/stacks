/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.GroupoidTarget
public import ReasLib.CategoryTheory.Fibered.InSetoids.Basic
public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Maps of setoid fibrations representable by algebraic spaces

A 1-morphism of categories fibred in setoids over `(Sch/S)_fppf` is representable
by algebraic spaces if and only if the induced map of fiberwise isomorphism-class
presheaves is, in the sense of Bootstrap Definition 80.3.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver
open Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Lemma 94.9.6: let `S` be an object of `Sch_fppf`. Let `f : X ⟶ Y` be a
1-morphism of categories fibred in setoids over `(Sch/S)_fppf`. Let `F` and `G`
be the presheaves `Functor.fiberIsoClassPresheaf X.p` and
`Functor.fiberIsoClassPresheaf Y.p` of fiberwise isomorphism classes, and let
`a` be the map of presheaves `BasedFunctor.fiberIsoClassMap (toBasedFunctor f)`
corresponding to `f`. Then `a` is representable by algebraic spaces in the
sense of Bootstrap Definition 80.3.1, encoded via Lemma 94.9.5 as relative
representability of the associated map of categories fibred in sets, if and only
if `f` is representable by algebraic spaces. -/
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

/-- Bootstrap Definition 80.3.1 for a `Type u` presentation of the fiberwise
isomorphism-class map of `f`, after identifying `Functor.fiberIsoClassPresheaf`
with a small presheaf whiskered by `uliftFunctor`. -/
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
