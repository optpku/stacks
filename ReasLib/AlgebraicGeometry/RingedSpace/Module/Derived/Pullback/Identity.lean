/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.MapIdentity
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition

/-! # Derived pullback along the identity of a ringed space -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.modulePullbackDerived

/-- The homotopy-level identity-pullback model is canonically isomorphic to the
derived localization functor. -/
noncomputable def idSourceIso (X : RingedSpace.{u}) :
    modulePullbackToDerived (𝟙 X) ≅
      (DerivedCategory.Qh : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤
        X.ModuleDerived) :=
  Functor.isoWhiskerRight
      ((Functor.mapHomotopyCategoryIso (RingedSpace.Hom.pullbackIdIso X)) ≪≫
        Functor.mapHomotopyCategoryIdIso X.Modules)
      (DerivedCategory.Qh : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤
        X.ModuleDerived) ≪≫
    Functor.leftUnitor _

/-- The canonical counit presenting the identity of `X.ModuleDerived` as a left-derived
model of pullback along `𝟙 X`. -/
noncomputable def idCounit (X : RingedSpace.{u}) :
    (DerivedCategory.Qh : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤
        X.ModuleDerived) ⋙
        Functor.id X.ModuleDerived ⟶ modulePullbackToDerived (𝟙 X) :=
  (Functor.rightUnitor _).hom ≫ (idSourceIso X).inv

/-- The identity functor with `idCounit` has the canonical left-derived universal property. -/
instance idFunctorIsLeftDerived (X : RingedSpace.{u}) :
    (Functor.id X.ModuleDerived).IsLeftDerivedFunctor
      (idCounit X) (RingedSpace.ModuleQis X) := sorry

/-- Derived pullback along the identity is canonically isomorphic to the identity functor. -/
noncomputable def idIso (X : RingedSpace.{u}) :
    modulePullbackDerived (𝟙 X) ≅ Functor.id X.ModuleDerived :=
  Functor.leftDerivedNatIso
    (modulePullbackDerived (𝟙 X)) (Functor.id X.ModuleDerived)
    ((modulePullbackToDerived (𝟙 X)).totalLeftDerivedCounit
      DerivedCategory.Qh (RingedSpace.ModuleQis X))
    (idCounit X) (RingedSpace.ModuleQis X) (Iso.refl _)

end AlgebraicGeometry.RingedSpace.modulePullbackDerived

