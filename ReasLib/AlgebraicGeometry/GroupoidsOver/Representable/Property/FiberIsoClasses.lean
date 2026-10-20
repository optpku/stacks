/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property.Presheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.FiberIsoClasses

/-!
# Morphism properties and fiberwise isomorphism classes

Compatible small presentations of the fiberwise isomorphism-class presheaves
of setoid fibrations preserve base-change-stable, fppf-target-local morphism
properties for maps representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- For compatible small presentations of the fiberwise isomorphism-class
presheaves of two setoid fibrations, a presented map representable by algebraic
spaces has a base-change-stable, fppf-target-local morphism property if and only
if the original morphism of setoid fibrations has that property. -/
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
