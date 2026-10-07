module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction

/-! # Absolute derived adjunctions on opens ringed sites -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

/-- On opens ringed sites, K-flat and K-injective resolutions give the two absolute
derived universal properties of module pullback and pushforward. These are the
composite-derived conditions for the canonical derived unit and counit, not the
mere existence of some adjunction between the two functors. -/
instance moduleDerivedAdjunctionHasPair {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    RingedSite.Hom.DerivedAdjunction.HasPair (opensRingedSiteHom f) := sorry

end AlgebraicGeometry.RingedSpace
