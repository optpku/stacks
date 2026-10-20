/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restriction of `𝒪_X`-modules along an étale scheme chart, viewed on the
underlying ringed space, is additive. -/
instance instAdditive_restrictToEtaleChart {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    (SmallEtaleModuleGlueing.restrictFunctor_hom U ⋙
      Modules.restrictToScheme U.left ⋙ Scheme.Modules.toRingedSpace U.left.left).Additive :=
  sorry


end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Derived restriction of an `𝒪_X`-module along an étale scheme chart, as a
complex of modules on the underlying ringed space of the chart, provided this
total left derived functor exists. -/
def restrictToEtaleChart {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X)
    [(Functor.Homotopy.toDerived
      (SmallEtaleModuleGlueing.restrictFunctor_hom U ⋙
      Modules.restrictToScheme U.left ⋙ Scheme.Modules.toRingedSpace U.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules X) (up ℤ))] :
    ModuleDerived X ⥤ RingedSpace.ModuleDerived U.left.left.toRingedSpace :=
  (Functor.Homotopy.toDerived
      (SmallEtaleModuleGlueing.restrictFunctor_hom U ⋙ Modules.restrictToScheme U.left ⋙
        Scheme.Modules.toRingedSpace U.left.left)).totalLeftDerived
    (DerivedCategory.Qh (C := Modules X))
      (HomotopyCategory.quasiIso (Modules X) (up ℤ))

/-- Derived restriction along an étale scheme chart is the total left derived
functor of underived chart restriction to the underlying ringed space. -/
theorem restrictToEtaleChart_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X)
    [(Functor.Homotopy.toDerived
      (SmallEtaleModuleGlueing.restrictFunctor_hom U ⋙
      Modules.restrictToScheme U.left ⋙ Scheme.Modules.toRingedSpace U.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules X) (up ℤ))] :
    restrictToEtaleChart U =
      (Functor.Homotopy.toDerived
          (SmallEtaleModuleGlueing.restrictFunctor_hom U ⋙ Modules.restrictToScheme U.left ⋙
            Scheme.Modules.toRingedSpace U.left.left)).totalLeftDerived
        (DerivedCategory.Qh (C := Modules X))
      (HomotopyCategory.quasiIso (Modules X) (up ℤ)) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
