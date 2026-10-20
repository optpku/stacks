/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}} {Λ : Type v} [CommRing Λ]
variable (j : U ⟶ X) [Etale j]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ))]

/-- Restriction along an étale morphism is additive on sheaves of modules. -/
instance etaleRestrictionSheaf_module_additive :
    @Functor.Additive _ _ _ _ Abelian.toPreadditive Abelian.toPreadditive
      (etaleRestrictionSheaf j (ModuleCat.{v} Λ)) := sorry

/-- Restriction along an étale morphism preserves finite colimits of module sheaves. -/
instance etaleRestrictionSheaf_module_preservesFiniteColimits :
    PreservesFiniteColimits (etaleRestrictionSheaf j (ModuleCat.{v} Λ)) := sorry

variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]

/-- Extension by zero along an étale morphism is additive on sheaves of modules. -/
instance moduleExtensionByZero_additive :
    @Functor.Additive _ _ _ _ Abelian.toPreadditive Abelian.toPreadditive
      (moduleExtensionByZero (Λ := Λ) j) := sorry

/-- Extension by zero along an étale morphism preserves finite limits of module sheaves. -/
instance moduleExtensionByZero_preservesFiniteLimits :
    PreservesFiniteLimits (moduleExtensionByZero (Λ := Λ) j) := sorry

/-- Extension by zero for étale module sheaves is left adjoint to restriction. -/
instance moduleExtensionByZero_isLeftAdjoint :
    (moduleExtensionByZero (Λ := Λ) j).IsLeftAdjoint := sorry

end AlgebraicGeometry.Scheme
