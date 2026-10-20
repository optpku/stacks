/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.CodimensionZero
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Sections

/-! # Codimension-zero decompositions of meromorphic module sheaves -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The direct image of the pullback of a module along a marked chart's canonical stalk map. -/
def codimZeroStalkPushforwardModule {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (F : X.Modules)
    (η : codimZeroPoints X) : X.Modules :=
  (Modules.pushforward (c η).stalkMap).obj ((Modules.pullback (c η).stalkMap).obj F)

/-- A stalk-module direct image is the composite of pullback and pushforward along the
canonical marked stalk map. -/
theorem codimZeroStalkPushforwardModule_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (F : X.Modules)
    (η : codimZeroPoints X) :
    codimZeroStalkPushforwardModule c F η =
      (Modules.pushforward (c η).stalkMap).obj ((Modules.pullback (c η).stalkMap).obj F) :=
  rfl

/-- The universe lift of a marked stalk-module direct image. -/
def codimZeroStalkPushforwardModuleLift {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (F : X.Modules)
    (η : codimZeroPoints X) : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  Modules.liftModule (codimZeroStalkPushforwardModule c F η)

/-- The lifted stalk-module direct image is obtained by the canonical module universe lift. -/
theorem codimZeroStalkPushforwardModuleLift_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (F : X.Modules)
    (η : codimZeroPoints X) :
    codimZeroStalkPushforwardModuleLift c F η =
      Modules.liftModule (codimZeroStalkPushforwardModule c F η) :=
  rfl

/-- The product of the lifted stalk-module direct images over codimension-zero points. -/
def codimZeroStalkPushforwardProductModule {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (F : X.Modules) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  ∏ᶜ fun η : codimZeroPoints X ↦ codimZeroStalkPushforwardModuleLift c F η

/-- The product of lifted stalk-module direct images is their categorical product. -/
theorem codimZeroStalkPushforwardProductModule_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (F : X.Modules) :
    codimZeroStalkPushforwardProductModule c F =
      ∏ᶜ fun η : codimZeroPoints X ↦ codimZeroStalkPushforwardModuleLift c F η :=
  rfl

/-- The coproduct of the lifted stalk-module direct images over codimension-zero points. -/
def codimZeroStalkPushforwardCoproductModule {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (F : X.Modules) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  ∐ fun η : codimZeroPoints X ↦ codimZeroStalkPushforwardModuleLift c F η

/-- The coproduct of lifted stalk-module direct images is their categorical coproduct. -/
theorem codimZeroStalkPushforwardCoproductModule_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (c : codimZeroPoints X → OpenImmersionChart X) (F : X.Modules) :
    codimZeroStalkPushforwardCoproductModule c F =
      ∐ fun η : codimZeroPoints X ↦ codimZeroStalkPushforwardModuleLift c F η :=
  rfl

/-- For valid charts at codimension-zero points, the coproduct of stalk-module direct images
agrees with their product if weakly associated points have codimension zero, irreducible
components are finite on compact étale opens, and these points have monomorphic field
representatives. -/
theorem codimZeroStalkPushforwardCoproduct_isIsomorphic_product {S : Scheme.{u}}
    {X : AlgebraicSpace S} [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (c : codimZeroPoints X → OpenImmersionChart X)
    (hc : ∀ η, Points.mapOfOver (c η).ι (c η).u = η) (F : X.Modules) :
    IsIsomorphic (codimZeroStalkPushforwardCoproductModule c F)
      (codimZeroStalkPushforwardProductModule c F) :=
  sorry

/-- Meromorphic sections of a quasi-coherent module form the product of its codimension-zero
stalk direct images after restriction of scalars, provided weakly associated points have
codimension zero, irreducible components are finite on compact étale opens, and
codimension-zero points have monomorphic field representatives. -/
theorem meromorphicSectionSheaf_iso_codimZeroStalkPushforwardProduct
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (c : codimZeroPoints X → OpenImmersionChart X)
    (hc : ∀ η, Points.mapOfOver (c η).ι (c η).u = η)
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIsomorphic
      ((restrictionAlong (toMeromorphicFunctionSheafHom X)).obj (meromorphicSectionSheaf X F))
      (codimZeroStalkPushforwardProductModule c F) :=
  sorry

/-- The meromorphic-function sheaf viewed as a structure-sheaf module by restriction of scalars. -/
def meromorphicFunctionModule {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  (restrictionAlong (toMeromorphicFunctionSheafHom X)).obj
    (unitModule (smallEtaleTopology X) (meromorphicFunctionSheaf X))

/-- If weakly associated points have codimension zero, irreducible components are finite on
compact étale opens, and codimension-zero points have monomorphic field representatives, there
are pointed open scheme charts at those points for which meromorphic functions and
quasi-coherent meromorphic sections are both coproducts and products of stalk direct images;
rational functions are the global meromorphic functions. -/
theorem meromorphic_codimZero_decomposition {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η) :
    ∃ c : codimZeroPoints X → OpenImmersionChart X,
      (∀ η, Points.mapOfOver (c η).ι (c η).u = η) ∧
      IsIsomorphic (meromorphicFunctionSheaf X) (codimZeroStalkPushforwardProductSheaf c) ∧
      IsIsomorphic (meromorphicFunctionModule X)
        (codimZeroStalkPushforwardCoproductModule c (SheafOfModules.unit (structureSheaf X))) ∧
      IsIsomorphic
        (codimZeroStalkPushforwardCoproductModule c (SheafOfModules.unit (structureSheaf X)))
        (codimZeroStalkPushforwardProductModule c (SheafOfModules.unit (structureSheaf X))) ∧
      (∀ (F : X.Modules) [F.IsQuasicoherent],
        IsIsomorphic
          ((restrictionAlong (toMeromorphicFunctionSheafHom X)).obj
            (meromorphicSectionSheaf X F))
          (codimZeroStalkPushforwardCoproductModule c F) ∧
        IsIsomorphic (codimZeroStalkPushforwardCoproductModule c F)
          (codimZeroStalkPushforwardProductModule c F)) ∧
      IsIsomorphic (rationalFunctionRing X) (meromorphicFunctions X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
