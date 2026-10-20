module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.SmallEtale

open CategoryTheory

universe u

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.SmallEtale.inclusion :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      AlgebraicGeometry.Scheme.DerivedQCoh.SmallEtale X ⥤
        DerivedCategory
          (RingedSite.ModuleCat.{u} (AlgebraicGeometry.Scheme.Etale.Small.ringedSite X)))
