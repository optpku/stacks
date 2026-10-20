module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.EtaleComparison

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The identity functor on module sheaves, viewed as modules on the opens ringed site. -/
abbrev toOpensModules (X : AlgebraicGeometry.Scheme.{u}) :
    X.toRingedSpace.Modules ⥤
      RingedSite.ModuleCat.{u} (AlgebraicGeometry.RingedSpace.opensRingedSite X.toRingedSpace) :=
  𝟭 X.toRingedSpace.Modules

end AlgebraicGeometry.Scheme.DerivedQCoh

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.epsilonStar_isEquivalence :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      Functor.IsEquivalence (AlgebraicGeometry.Scheme.DerivedQCoh.epsilonStar X))
