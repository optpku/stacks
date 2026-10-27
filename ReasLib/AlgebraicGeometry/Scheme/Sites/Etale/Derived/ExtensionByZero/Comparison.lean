/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZeroComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ModuleSheaf
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain

/-!
# The derived comparison from extension by zero to direct image

For a separated étale morphism, the canonical sheaf comparison descends through
the exact extension-by-zero functor to a comparison with derived direct image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U T : Scheme.{u}} (j : U ⟶ T) [Etale j] [IsSeparated j]
variable {Λ : Type u} [Ring Λ]
variable [HasSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : U.Etale, HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ, (etaleRestriction j).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero j (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ))]

/-- The canonical comparison from exact extension by zero to derived direct image
along a separated étale morphism, induced by the sheaf comparison and the
cochain right-derived unit. -/
def moduleDerivedExtensionByZeroToDirectImage :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory ⟶
      etaleDerivedPushforward j :=
  ((etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory).rightDerivedDesc
    ((etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategoryFactors.inv)
    (HomologicalComplex.quasiIso
      (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (etaleDerivedPushforward j)
    (whiskerRight
        (NatTrans.mapHomologicalComplex
          (moduleExtensionByZeroToDirectImage (Λ := Λ) j)
          (ComplexShape.up ℤ))
        (DerivedCategory.Q :
          CochainComplex
            (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
            DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))) ≫
      RightDerived.Cochain.unit
        ((smallEtalePullback j).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) T.smallEtaleTopology
          U.smallEtaleTopology))

/-- The derived comparison is the descent of the sheaf comparison followed by
the cochain right-derived unit. -/
theorem moduleDerivedExtensionByZeroToDirectImage_eq :
    moduleDerivedExtensionByZeroToDirectImage (Λ := Λ) j =
      ((etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory).rightDerivedDesc
    ((etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategoryFactors.inv)
    (HomologicalComplex.quasiIso
      (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (etaleDerivedPushforward j)
    (whiskerRight
        (NatTrans.mapHomologicalComplex
          (moduleExtensionByZeroToDirectImage (Λ := Λ) j)
          (ComplexShape.up ℤ))
        (DerivedCategory.Q :
          CochainComplex
            (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
            DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))) ≫
      RightDerived.Cochain.unit
        ((smallEtalePullback j).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) T.smallEtaleTopology
          U.smallEtaleTopology)) := rfl

end AlgebraicGeometry.Scheme.Etale

end
