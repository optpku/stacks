/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

variable {A B C : Scheme.{u}} (j : A ⟶ B) (k : B ⟶ C) [Etale j] [Etale k]
variable (Λ : Type v) [CommRing Λ]

/-- Sheaf restriction along a composite étale morphism is iterated restriction. -/
def etaleRestrictionSheafCompIso :
    etaleRestrictionSheaf k (ModuleCat.{v} Λ) ⋙
      etaleRestrictionSheaf j (ModuleCat.{v} Λ) ≅
    etaleRestrictionSheaf (j ≫ k) (ModuleCat.{v} Λ) :=
  Functor.sheafPushforwardContinuousComp'
    (show etaleRestriction j ⋙ etaleRestriction k ≅ etaleRestriction (j ≫ k) from
      (MorphismProperty.Over.mapComp (⊤ : MorphismProperty Scheme)
      (inferInstance : Etale j) (inferInstance : Etale k) (j ≫ k) rfl).symm)
    (ModuleCat.{v} Λ) A.smallEtaleTopology B.smallEtaleTopology C.smallEtaleTopology

variable [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [HasWeakSheafify C.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ F : A.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : B.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction k).op.HasLeftKanExtension F]
variable [∀ F : A.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction (j ≫ k)).op.HasLeftKanExtension F]

/-- Extension by zero along a composite étale morphism is iterated extension
by zero, via the canonical comparison of left adjoints. -/
def etaleExtensionByZeroCompIso :
    etaleExtensionByZero j (ModuleCat.{v} Λ) ⋙
      etaleExtensionByZero k (ModuleCat.{v} Λ) ≅
    etaleExtensionByZero (j ≫ k) (ModuleCat.{v} Λ) :=
  Adjunction.leftAdjointCompIso
    (etaleExtensionByZero_adjunction j (ModuleCat.{v} Λ))
    (etaleExtensionByZero_adjunction k (ModuleCat.{v} Λ))
    (etaleExtensionByZero_adjunction (j ≫ k) (ModuleCat.{v} Λ))
    (etaleRestrictionSheafCompIso j k Λ)

end AlgebraicGeometry.Scheme.Etale

end
