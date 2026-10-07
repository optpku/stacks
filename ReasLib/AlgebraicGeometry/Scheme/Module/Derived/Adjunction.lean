module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- A morphism of schemes has the canonical derived pullback-pushforward adjunction pair. -/
theorem derivedAdjunctionHasPair (f : X ⟶ Y) :
    RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom) := sorry

/-- The canonical derived pullback-pushforward adjunction associated to a scheme morphism. -/
noncomputable def derivedAdjunction (f : X ⟶ Y) :
    RingedSpace.modulePullbackDerived f.toShHom ⊣
      RingedSpace.moduleDerivedPushforward f.toShHom :=
  @RingedSpace.modulePullbackDerivedPushforwardAdjunction _ _
    f.toShHom _ _ _ _ _ _ _ (derivedAdjunctionHasPair f)

end AlgebraicGeometry.Scheme.Hom
