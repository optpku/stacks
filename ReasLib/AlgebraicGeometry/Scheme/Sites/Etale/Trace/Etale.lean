/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.FiberWeight
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZeroStalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.EtaleAdjunction

/-! # Fibre-weight traces along étale morphisms are adjunction counits -/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback j).op.HasLeftKanExtension P]

/-- The fibre-weight trace on abelian étale sheaves equals the extension-by-zero
counit transported through the canonical finite-support and inverse-image comparisons. -/
theorem fiberWeightTraceHom_eq_abelianEtaleTrace
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (extensionByZeroIsoLowerShriek j).inv.app
        ((etaleAbelianSheafPullback j).obj F) ≫
      (abelianExtensionByZero j).map
        ((etaleRestrictionSheafIso_smallEtalePullback j F).inv) ≫
      (abelianEtaleTrace j).app F =
      fiberWeightTraceHom j F := sorry

variable (Λ : Type u) [CommRing Λ]
variable [U.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback j).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction j).op]
variable [∀ V : U.Etale,
  HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ V : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- The derived fibre-weight trace along an étale morphism equals the counit of
the finite-support direct-image and inverse-image adjunction. -/
theorem fiberWeightTraceDerivedHom_eq_counit
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    fiberWeightTraceDerivedHom j Λ K =
      (lowerShriekModuleDerivedEtaleAdjunction j Λ).counit.app K := sorry

end AlgebraicGeometry.Scheme.Etale

end
