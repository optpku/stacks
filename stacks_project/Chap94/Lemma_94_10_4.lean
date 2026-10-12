/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.GroupoidTarget
public import ReasLib.CategoryTheory.Fibered.InSetoids.Basic
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap80.Definition_80_4_1_Relative
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Properties of setoid-fibration morphisms versus iso-class maps

A 1-morphism of categories fibred in setoids over `(Sch/S)_fppf` has a morphism
property `P` in the Definition 94.10.1 sense if and only if the induced map of
fiberwise isomorphism-class presheaves has `P` in the Bootstrap 80.4.1 sense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 94.10.4: let `S` be an object of `Sch_fppf`. Let `P` be as in
Definition 94.10.1. Let `f : X ⟶ Y` be a 1-morphism of categories fibred in
setoids over `(Sch/S)_fppf`. Let `F` and `G` be `Type u` presentations of the
presheaves of fiberwise isomorphism classes `Functor.fiberIsoClassPresheaf X.p`
and `Functor.fiberIsoClassPresheaf Y.p`, identified after `uliftFunctor`, and
let `a : F ⟶ G` be the corresponding map of presheaves, so that
`BasedFunctor.fiberIsoClassMap (toBasedFunctor f)` matches `a` after whiskering
by `uliftFunctor`. If `a` is representable by algebraic spaces, then `a` has
property `P` in the Bootstrap 80.4.1 sense if and only if `f` has property `P`
in the Definition 94.10.1 sense. -/
@[stacks 04TC]
theorem has.iff_fiberIsoClassMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [Functor.IsFibered.InSetoids X.p] [Functor.IsFibered.InSetoids Y.p]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (f : X ⟶ Y) {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (iX : Functor.fiberIsoClassPresheaf X.p ≅ F ⋙ uliftFunctor.{u + 1, u})
    (iY : Functor.fiberIsoClassPresheaf Y.p ≅ G ⋙ uliftFunctor.{u + 1, u})
    (h_map : BasedFunctor.fiberIsoClassMap (toBasedFunctor f) =
      iX.hom ≫ Functor.whiskerRight a uliftFunctor.{u + 1, u} ≫ iY.inv)
    (ha : AlgebraicSpace.representableByAlgebraicSpaces a) :
    ha.has P ↔ has P f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
