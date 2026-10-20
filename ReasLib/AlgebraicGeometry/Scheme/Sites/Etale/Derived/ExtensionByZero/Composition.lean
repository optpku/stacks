/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

variable {A B C : Scheme.{u}} (j : A ⟶ B) (k : B ⟶ C) [Etale j] [Etale k]
variable (Λ : Type v) [CommRing Λ]

variable [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [HasWeakSheafify C.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ F : A.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : B.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction k).op.HasLeftKanExtension F]
variable [∀ F : A.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction (j ≫ k)).op.HasLeftKanExtension F]

variable [Abelian (Sheaf A.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf B.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf C.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf C.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero j (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero k (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero k (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero k (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (j ≫ k) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (j ≫ k) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (j ≫ k) (ModuleCat.{v} Λ))]

/-- Derived extension by zero along a composite étale morphism is the
composite of the derived extension-by-zero functors. -/
def etaleDerivedExtensionByZeroCompIso :
    etaleDerivedExtensionByZero j Λ ⋙ etaleDerivedExtensionByZero k Λ ≅
      etaleDerivedExtensionByZero (j ≫ k) Λ :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
    (ExactFunctor.of (etaleExtensionByZero j (ModuleCat.{v} Λ)))
    (ExactFunctor.of (etaleExtensionByZero k (ModuleCat.{v} Λ)))).symm ≪≫
  Functor.MapDerivedCategory.functorIso (etaleExtensionByZeroCompIso j k Λ)

end AlgebraicGeometry.Scheme.Etale

end
