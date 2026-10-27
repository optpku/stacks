/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Abelian

/-! # Leray comparison for abelian-valued derived global sections -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.Functor
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated ComplexShape TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Canonical Leray comparison `RΓ(B, Rf_* -) ⟶ RΓ(X, -)` in `D(Ab.{u})` for an
arbitrary morphism of algebraic spaces. -/
def moduleDerivedLerayComparison (f : X ⟶ B) :
    Modules.moduleDerivedPushforward f ⋙ moduleDerivedGlobalSectionsAb B ⟶
      moduleDerivedGlobalSectionsAb X :=
  (Modules.moduleDerivedPushforward f ⋙ moduleDerivedGlobalSectionsAb B).rightDerivedDesc
    (derivedGammaPushforwardCompositeUnit f)
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (moduleDerivedGlobalSectionsAb X)
    (whiskerRight (NatTrans.mapHomologicalComplex (gammaPushforwardComparison f) (up ℤ))
        DerivedCategory.Q ≫
      Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsAb X))

/-- `moduleDerivedLerayComparison` is the right-derived descent of the underived
global-sections comparison. -/
theorem moduleDerivedLerayComparison_eq (f : X ⟶ B) :
    moduleDerivedLerayComparison f =
      (Modules.moduleDerivedPushforward f ⋙ moduleDerivedGlobalSectionsAb B).rightDerivedDesc
        (derivedGammaPushforwardCompositeUnit f)
        (HomologicalComplex.quasiIso X.Modules (up ℤ))
        (moduleDerivedGlobalSectionsAb X)
        (whiskerRight (NatTrans.mapHomologicalComplex (gammaPushforwardComparison f) (up ℤ))
            DerivedCategory.Q ≫
          Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsAb X)) :=
  rfl

/-- The general-morphism Leray comparison `RΓ(B, Rf_* -) ⟶ RΓ(X, -)` is an isomorphism. -/
instance isIso_moduleDerivedLerayComparison (f : X ⟶ B) :
    IsIso (moduleDerivedLerayComparison f) :=
  sorry

/-- Degree-`n` cohomology of the Leray comparison at a derived module on `X`. -/
def moduleDerivedLerayComparison_app (f : X ⟶ B) (W : ModuleDerived X) (n : ℤ) :
    cohomologyAb B ((Modules.moduleDerivedPushforward f).obj W) n ⟶ cohomologyAb X W n :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
    ((moduleDerivedLerayComparison f).app W)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
