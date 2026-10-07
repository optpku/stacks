module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

/-!
# Derived pullback-pushforward adjunction for quasicoherent cohomology

The ambient derived pullback-pushforward adjunction on module sheaves restricts to the full
subcategories of derived modules with quasicoherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The canonical absolute-derived pair condition for the pullback and pushforward attached
to a morphism of schemes. -/
theorem pullbackPushforwardAdjunctionHasPair
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom) := sorry

/-- Derived pullback is left adjoint to derived pushforward after restricting both functors
to derived modules with quasicoherent cohomology. -/
noncomputable def pullbackPushforwardAdjunction
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    pullback f ⊣ pushforwardCohomologyIn f :=
  -- Local instance justification (proof-local temporary data): required only to construct the restricted adjunction.
  letI := pullbackPushforwardAdjunctionHasPair f
  ObjectProperty.FullSubcategory.adjunction
    (RingedSpace.modulePullbackDerived f.toShHom)
    (RingedSpace.moduleDerivedPushforward f.toShHom)
    (RingedSpace.modulePullbackDerivedPushforwardAdjunction f.toShHom)
    (pullback.mapsTo f) (pushforwardCohomologyIn.mapsTo f)

end AlgebraicGeometry.Scheme.DerivedQCoh
