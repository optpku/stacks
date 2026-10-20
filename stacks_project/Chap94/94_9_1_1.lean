/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.Setoids.AssociatedSets.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.OnSpace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory CategoryTheory.TwoFibreProduct

universe u

/- 94.9.1.1: choose an algebraic space `Fy` representing the slice base change
of `f` along `y`, with structure morphism `fy : Fy ⟶ ofOver U`. The representing
equivalence identifies the first projection with `fy` via `ofOverSliceEquiv`.
The right square is the canonical 2-commutative 2-fibre product, with projections
`TwoFibreProduct.fst` and `TwoFibreProduct.snd` and invertible comparison cell
`TwoFibreProduct.comparisonIso`; its universal property is
`TwoFibreProduct.cone.isBilimit`. The leftward squiggly arrows pass to the
associated sheaf of isomorphism classes, using `Functor.fiberIsoClassPresheaf`
and `FiberedCategoryOver.Setoids.associatedSets`. The on-space comparison below
identifies both presheaves with the functors of points of `Fy` and `ofOver U`
after universe lift, and carries the canonical first projection to `fy`. -/
@[stacks 0402]
#check (AlgebraicGeometry.RepresentsBaseChange.projection_triangle :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} {f : X ⟶ Y} {U : Over S}
    {y : GroupoidsOver.slice U ⟶ Y} {Fy : AlgebraicSpace S} {fy : Fy ⟶ ofOver U},
    RepresentsBaseChange f y Fy fy →
      ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ Fy.toGroupoids,
        Nonempty
          (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv U).hom ≅
            TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f))

section
variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
variable {U : Over S} (y : GroupoidsOver.slice U ⟶ Y)
variable (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U)

#check (CategoryTheory.TwoFibreProduct.cone.{u + 1, u, u + 1, u} y f :
  Bicategory.PseudoPullbackCone y f)
#check (CategoryTheory.TwoFibreProduct.cone.isBilimit.{u + 1, u, u + 1, u} y f :
  (TwoFibreProduct.cone.{u + 1, u, u + 1, u} y f).IsBilimit)
#check (CategoryTheory.TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f :
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ⟶ GroupoidsOver.slice U)
#check (CategoryTheory.TwoFibreProduct.snd.{u + 1, u, u + 1, u} y f :
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ⟶ X)
#check (CategoryTheory.TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} y f :
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f ≫ y ≅
    TwoFibreProduct.snd.{u + 1, u, u + 1, u} y f ≫ f)

#check (AlgebraicGeometry.AlgebraicSpace.ofOverSliceEquiv U :
  (ofOver U).toGroupoids ≌ GroupoidsOver.slice U)
#check (AlgebraicGeometry.AlgebraicSpace.toGroupoids Fy : GroupoidsOver S)
#check (AlgebraicGeometry.RepresentsBaseChange.apex_equivalence :
  RepresentsBaseChange f y Fy fy →
    Nonempty (TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ Fy.toGroupoids))

#check (AlgebraicGeometry.RepresentsTwoFibreProductOnSpace.of_representsBaseChange :
  RepresentsBaseChange f y Fy fy →
    RepresentsTwoFibreProductOnSpace f y Fy (ofOver U) fy)
#check (AlgebraicGeometry.RepresentsTwoFibreProductOnSpace.fiberIsoClass_ulift :
  RepresentsTwoFibreProductOnSpace f y Fy (ofOver U) fy →
    ∃ (iU : Functor.fiberIsoClassPresheaf
          (FiberedCategoryOver.Groupoids.p (GroupoidsOver.slice U)) ≅
        (ofOver U).functorOfPoints ⋙ uliftFunctor.{u + 1, u})
      (iApex : Functor.fiberIsoClassPresheaf
          (FiberedCategoryOver.Groupoids.p
            (TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f)) ≅
        Fy.functorOfPoints ⋙ uliftFunctor.{u + 1, u}),
      BasedFunctor.fiberIsoClassMap
          (FiberedCategoryOver.Groupoids.toBasedFunctor
            (TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f)) =
        iApex.hom ≫ Functor.whiskerRight fy uliftFunctor.{u + 1, u} ≫ iU.inv)

#check (CategoryTheory.Functor.fiberIsoClassPresheaf
    (FiberedCategoryOver.Groupoids.p
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f)) :
  (Over S)ᵒᵖ ⥤ Type (u + 1))
#check (CategoryTheory.FiberedCategoryOver.Setoids.associatedSets :
  FiberedCategoryOver.Setoids (Over S) → FiberedCategoryOver.Sets (Over S))
#check (CategoryTheory.FiberedCategoryOver.Groupoids.baseChange f y :
  FiberedCategoryOver.Groupoids (Over U))
end
