module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Open restrictions of morphisms of groupoid fibrations -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Restriction of the 2-Yoneda 1-morphism of `x` along an open immersion
`U' ⟶ U`. -/
def restrictToOpen {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}}
    (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU) (U' : U.Opens) :
    GroupoidsOver.slice (Over.mk (U'.ι ≫ hU)) ⟶ X :=
  overMap (Over.homMk U'.ι rfl : Over.mk (U'.ι ≫ hU) ⟶ Over.mk hU) ≫
    yonedaOfObject hU x hx

/-- Unfolding `restrictToOpen` recovers precomposition of `yonedaOfObject` with
`overMap` of the open inclusion. -/
theorem restrictToOpen_spec {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (U' : U.Opens) :
    restrictToOpen hU x hx U' =
      overMap (Over.homMk U'.ι rfl : Over.mk (U'.ι ≫ hU) ⟶ Over.mk hU) ≫
        yonedaOfObject hU x hx := rfl

end AlgebraicGeometry.GroupoidsOver
