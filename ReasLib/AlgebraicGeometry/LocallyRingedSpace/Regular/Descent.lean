/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.RingTheory.EssentialFiniteness.Basic
public import ReasLib.RingTheory.RegularLocalRing.Flat

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.Hom

/-- Regular-locality of stalks descends along a point-surjective flat morphism of locally
ringed spaces whose stalk maps are essentially of finite presentation. -/
theorem regular_of_flat_of_surjective
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    [RingedSpace.Hom.IsFlat f.toShHom]
    (h_lfp : ∀ x : X, (f.stalkMap x).hom.EssFinitePresentation)
    (h_surjective : Function.Surjective f.base)
    (h_regular : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) :
    ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) := sorry

end AlgebraicGeometry.LocallyRingedSpace.Hom
