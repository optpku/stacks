/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Lemma_61_19_8_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.19.8

The essential image of `ε⁻¹` on sheaves of `Λ`-modules is a weak Serre
subcategory, and derived inverse image implements an equivalence
`D⁺(X.Etale, Λ) ≌ D⁺_C(X.ProEt, Λ)` with quasi-inverse `Rε_*`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [PreservesFiniteLimits (etaleToProEtPullback X (ModuleCat.{u + 1} Λ))]
variable [PreservesFiniteColimits (etaleToProEtPullback X (ModuleCat.{u + 1} Λ))]

/-- Lemma 61.19.8 (1): for a scheme `X` and a ring `Λ`, the essential image
`etaleToProEtModuleEssImage X Λ` of the fully faithful functor
`ε⁻¹ = etaleToProEtPullback X (ModuleCat Λ)` from sheaves of `Λ`-modules on
`X.Etale` to sheaves of `Λ`-modules on `X.ProEt` is a weak Serre subcategory. -/
@[stacks 09B1]
instance etaleToProEtModuleEssImage_isWeakSerre :
    IsWeakSerreClass (etaleToProEtModuleEssImage X Λ) :=
  sorry

/-- Lemma 61.19.8 (2): for a scheme `X` and a ring `Λ`, derived inverse image
`etaleToProEt_modulePlusPullbackLift` is an equivalence
`D⁺(X.Etale, Λ) ≌ D⁺_C(X.ProEt, Λ)` with quasi-inverse
`Rε_* = etaleToProEt_modulePlusPushforwardRestrict`. -/
@[stacks 09B1]
instance etaleToProEt_modulePlusPullbackLift_isEquivalence :
    Functor.IsEquivalence (etaleToProEt_modulePlusPullbackLift X Λ) :=
  sorry

/-- The derived adjunction unit `K ⟶ Rε_* ε⁻¹ K` is an isomorphism on every
object of `D⁺(X.Etale, Λ)`. -/
instance etaleToProEt_modulePlusAdjunction_unit_app_isIso
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((etaleToProEt_modulePlusAdjunction X Λ).unit.app K) :=
  sorry

/-- The derived adjunction counit is an isomorphism on every object of
`D⁺_C(X.ProEt, Λ)`, so `Rε_* = etaleToProEt_modulePlusPushforwardRestrict` is a
quasi-inverse of `etaleToProEt_modulePlusPullbackLift`. -/
instance etaleToProEt_modulePlusAdjunction_counit_app_isIso
    (K : DerivedCategory.Plus.CohomologyIn (etaleToProEtModuleEssImage X Λ)) :
    IsIso
      ((etaleToProEt_modulePlusAdjunction X Λ).counit.app
        ((DerivedCategory.Plus.cohomologyIn (etaleToProEtModuleEssImage X Λ)).ι.obj K)) :=
  sorry

end AlgebraicGeometry.Scheme

end

end
