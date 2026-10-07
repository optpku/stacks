module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- The compatibility import exposes arbitrary derived pullback preservation with the
source-facing aliases. -/
#check (pullback.mapsTo :
  ∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
    derivedQuasiCoherentModuleProperty X ≤
      (derivedQuasiCoherentModuleProperty Y).inverseImage
        (RingedSpace.modulePullbackDerived f.toLRSHom.toShHom))

end AlgebraicGeometry.Scheme.DerivedQCoh
