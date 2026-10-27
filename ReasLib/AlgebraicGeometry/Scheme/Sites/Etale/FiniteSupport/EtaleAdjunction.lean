/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.ModuleExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LocallyQuasiFinite
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousLeftAdjoint

/-! # Étale finite-support adjunctions for module sheaves -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
variable (Λ : Type u) [Ring Λ]
variable [HasWeakSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]

/-- Restriction of étale module sheaves is naturally isomorphic to inverse image. -/
def etaleModuleRestrictionIsoInverseImage :
    etaleRestrictionSheaf j (ModuleCat.{u} Λ) ≅
      Sheaf.smallEtaleInverseImage j (ModuleCat.{u} Λ) :=
  Functor.isoWhiskerLeft (etaleRestrictionSheaf j (ModuleCat.{u} Λ))
      (sheafificationNatIso U.smallEtaleTopology (ModuleCat.{u} Λ)) ≪≫
    Functor.isoWhiskerRight
      ((etaleRestriction j).sheafPushforwardContinuousCompSheafToPresheafIso
        (ModuleCat.{u} Λ) U.smallEtaleTopology X.smallEtaleTopology)
      (presheafToSheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) ≪≫
    (Functor.LeftAdjoint.pullbackIsoCocontinuous
      (smallEtalePullback j) (etaleRestriction j)
      (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
        (inferInstance : Etale j) trivial) (ModuleCat.{u} Λ)).symm

variable [U.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction j).op]

/-- Finite-support direct image along an étale morphism is left adjoint to
inverse image on module sheaves. -/
def lowerShriekModuleEtaleAdjunction :
    lowerShriekModule j Λ ⊣ Sheaf.smallEtaleInverseImage j (ModuleCat.{u} Λ) :=
  ((etaleExtensionByZero_adjunction j (ModuleCat.{u} Λ)).ofNatIsoLeft
    (lowerShriekModuleIsoExtensionByZero j Λ)).ofNatIsoRight
      (etaleModuleRestrictionIsoInverseImage j Λ)

variable [∀ V : U.Etale,
  HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ V : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived finite-support direct image along an étale morphism is left adjoint
to derived inverse image on module sheaves. -/
def lowerShriekModuleDerivedEtaleAdjunction :
    lowerShriekModuleDerived j Λ ⊣ etaleModuleDerivedInverseImage j Λ :=
  Adjunction.mapDerivedCategory (lowerShriekModuleEtaleAdjunction j Λ)

end AlgebraicGeometry.Scheme.Etale

end
