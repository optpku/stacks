/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Exact
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.PullbackStalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Stalk
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition.ExactFirst

/-!
# Derived pullback on stalks

This module identifies the stalk of a derived pullback with derived extension of scalars
between the corresponding stalk rings.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor.LeftDerived.Homotopy.Composition

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.modulePullbackDerived.Stalk

variable {Y Z : RingedSpace.{u}} (p : Y ⟶ Z) (y : Y)

/-- The pullback-stalk isomorphism is natural in the source module. -/
theorem naturality {M N : Z.Modules} (φ : M ⟶ N) :
    ((RingedSpace.stalkModuleFunctor (p.hom.base y) ⋙
        ModuleCat.extendScalars (p.hom.stalkMap y).hom).map φ) ≫
          (RingedSpace.Hom.pullbackStalkIso p N y).hom =
      (RingedSpace.Hom.pullbackStalkIso p M y).hom ≫
        ((RingedSpace.Hom.pullback p ⋙ RingedSpace.stalkModuleFunctor y).map φ) := sorry

/-- Pullback followed by a stalk is naturally identified with extension of the source stalk. -/
noncomputable def underivedIso :
    RingedSpace.stalkModuleFunctor (p.hom.base y) ⋙
        ModuleCat.extendScalars (p.hom.stalkMap y).hom ≅
      RingedSpace.Hom.pullback p ⋙ RingedSpace.stalkModuleFunctor y :=
  NatIso.ofComponents (fun M ↦ RingedSpace.Hom.pullbackStalkIso p M y)
    (fun φ ↦ naturality p y φ)

/-- The canonical counit for taking a derived stalk and then extending scalars. -/
noncomputable def extensionRouteCounit :
    (DerivedCategory.Qh : HomotopyCategory Z.Modules (ComplexShape.up ℤ) ⥤
        DerivedCategory Z.Modules) ⋙
        (RingedSpace.ModuleDerived.Stalk.functor (p.hom.base y) ⋙
          ModuleCat.derivedExtensionOfScalars (p.hom.stalkMap y).hom) ⟶
      Functor.Homotopy.toDerived
        (RingedSpace.stalkModuleFunctor (p.hom.base y) ⋙
          ModuleCat.extendScalars (p.hom.stalkMap y).hom) :=
  ExactFirst.counit
    (ExactFunctor.of (RingedSpace.stalkModuleFunctor (p.hom.base y)))
    (ModuleCat.extendScalars (p.hom.stalkMap y).hom)

/-- The canonical counit for derived pullback followed by the exact stalk functor. -/
noncomputable def pullbackRouteCounit :
    (DerivedCategory.Qh : HomotopyCategory Z.Modules (ComplexShape.up ℤ) ⥤
        DerivedCategory Z.Modules) ⋙
        (RingedSpace.modulePullbackDerived p ⋙
          RingedSpace.ModuleDerived.Stalk.functor y) ⟶
      Functor.Homotopy.toDerived
        (RingedSpace.Hom.pullback p ⋙ RingedSpace.stalkModuleFunctor y) :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((RingedSpace.modulePullbackToDerived p).totalLeftDerivedCounit
        DerivedCategory.Qh (RingedSpace.ModuleQis Z)) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (RingedSpace.stalkModuleFunctor y).mapDerivedCategoryFactorsh.hom ≫
    (toDerivedIso
      (RingedSpace.stalkModuleFunctor y) (RingedSpace.Hom.pullback p)
      (RingedSpace.Hom.pullback p ⋙ RingedSpace.stalkModuleFunctor y) (Iso.refl _)).inv

/-- The derived stalk-extension route has the universal property of the derived composite. -/
instance extensionRouteIsLeftDerived :
    (RingedSpace.ModuleDerived.Stalk.functor (p.hom.base y) ⋙
      ModuleCat.derivedExtensionOfScalars (p.hom.stalkMap y).hom).IsLeftDerivedFunctor
        (extensionRouteCounit p y) (RingedSpace.ModuleQis Z) := sorry

/-- The derived-pullback-then-stalk route has the universal property of the derived composite. -/
instance pullbackRouteIsLeftDerived :
    (RingedSpace.modulePullbackDerived p ⋙
      RingedSpace.ModuleDerived.Stalk.functor y).IsLeftDerivedFunctor
        (pullbackRouteCounit p y) (RingedSpace.ModuleQis Z) := sorry

/-- Derived pullback followed by a stalk is canonically identified with derived scalar
extension of the source stalk. -/
noncomputable def iso :
    RingedSpace.ModuleDerived.Stalk.functor (p.hom.base y) ⋙
        ModuleCat.derivedExtensionOfScalars (p.hom.stalkMap y).hom ≅
      RingedSpace.modulePullbackDerived p ⋙
        RingedSpace.ModuleDerived.Stalk.functor y :=
  Functor.leftDerivedNatIso
    (RingedSpace.ModuleDerived.Stalk.functor (p.hom.base y) ⋙
      ModuleCat.derivedExtensionOfScalars (p.hom.stalkMap y).hom)
    (RingedSpace.modulePullbackDerived p ⋙
      RingedSpace.ModuleDerived.Stalk.functor y)
    (extensionRouteCounit p y) (pullbackRouteCounit p y)
    (RingedSpace.ModuleQis Z)
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso (underivedIso p y))
      (DerivedCategory.Qh : HomotopyCategory (ModuleCat (Y.presheaf.stalk y))
        (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat (Y.presheaf.stalk y))))

end AlgebraicGeometry.RingedSpace.modulePullbackDerived.Stalk

end
