/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import stacks_project.Chap92.Lemma_92_26_4_Comparison
public import stacks_project.Chap92.Lemma_92_27_3_Omega

/-!
# Derived lower shriek of naive differentials on `C_{X/Λ}`

This leaf owns `Lπ_!` of `underline{𝒪}_X`-modules on `C_{X/Λ}`, the derived inverse
image `Li^*` along `i♯`, and the identifications `Li^* Ω = i^* Ω = Ω ⊗_O underline{𝒪}_X`
in `D(underline{𝒪}_X)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open RingedSite.Cocontinuous
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))

/-- The inverse-image ring sheaf `forget⁻¹ 𝒪_X` on `C_{X/Λ}`, as a module coefficient
for `Lπ_!` landing in `D(𝒪_X)`. -/
abbrev underlineInverseImageRing : Sheaf (topology Λ X) RingCat.{u + 1} :=
  inverseImageRingSheaf (forget Λ X) (ringOf (commStructureSheafLift X))

/-- `underlineInverseImageRing` is inverse image of the lifted structure sheaf of `X`. -/
theorem underlineInverseImageRing_eq :
    underlineInverseImageRing Λ X =
      inverseImageRingSheaf (forget Λ X) (ringOf (commStructureSheafLift X)) :=
  rfl

/-- The ringed site `(C_{X/Λ}, forget⁻¹ 𝒪_X)` used as the source of `Lπ_!`. -/
abbrev underlineInverseImageSite : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf (topology Λ X) (underlineInverseImageRing Λ X)

/-- Unfolding of `underlineInverseImageSite`. -/
theorem underlineInverseImageSite_eq :
    underlineInverseImageSite Λ X =
      RingedSite.ofRingSheaf (topology Λ X) (underlineInverseImageRing Λ X) :=
  rfl

/-- Comparison of commutative `underline{𝒪}_X` with `forget⁻¹ 𝒪_X` on underlying rings. -/
def underlineRingComparison :
    ringSheaf.{u + 1, u, u + 1} (topology Λ X) (underlineSheafLift Λ X) ⟶
      underlineInverseImageRing Λ X :=
  ObjectProperty.homMk
    { app := fun _ ↦ 𝟙 _
      naturality := fun _ _ _ ↦ sorry }

/-- The inverse comparison `forget⁻¹ 𝒪_X ⟶ underline{𝒪}_X` on underlying rings. -/
def underlineRingComparisonInv :
    underlineInverseImageRing Λ X ⟶
      ringSheaf.{u + 1, u, u + 1} (topology Λ X) (underlineSheafLift Λ X) :=
  ObjectProperty.homMk
    { app := fun _ ↦ 𝟙 _
      naturality := fun _ _ _ ↦ sorry }

/-- `underlineRingComparison` and `underlineRingComparisonInv` are inverse. -/
def underlineRingIso :
    ringSheaf.{u + 1, u, u + 1} (topology Λ X) (underlineSheafLift Λ X) ≅
      underlineInverseImageRing Λ X where
  hom := underlineRingComparison Λ X
  inv := underlineRingComparisonInv Λ X
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Unfolding of the forward map of `underlineRingIso`. -/
theorem underlineRingIso_hom :
    (underlineRingIso Λ X).hom = underlineRingComparison Λ X :=
  rfl

/-- `omegaTensor`, viewed as a module over `forget⁻¹ 𝒪_X`. -/
def omegaTensorInverseImage :
    RingedSite.ModuleCat.{u + 1} (underlineInverseImageSite Λ X) :=
  (SheafOfModules.ChangeOfRings.extendScalars.{u + 1, u, u + 1, u + 1}
      (underlineRingComparison Λ X)).obj (omegaTensor Λ X)

/-- Unfolding of `omegaTensorInverseImage`. -/
theorem omegaTensorInverseImage_eq :
    omegaTensorInverseImage Λ X =
      (SheafOfModules.ChangeOfRings.extendScalars.{u + 1, u, u + 1, u + 1}
          (underlineRingComparison Λ X)).obj (omegaTensor Λ X) :=
  rfl

/-- The forgetful functor is continuous from the inherited topology on `C_{X/Λ}` to
the small étale topology. -/
instance forget_isContinuous :
    (forget Λ X).IsContinuous (topology Λ X) (smallEtaleTopology X) :=
  Functor.inheritedTopology.isContinuous (forget Λ X) (smallEtaleTopology X)

/-- The forgetful functor is cocontinuous from the inherited topology on `C_{X/Λ}` to
the small étale topology. -/
instance forget_isCocontinuous :
    (forget Λ X).IsCocontinuous (topology Λ X) (smallEtaleTopology X) :=
  Functor.inheritedTopology.isCocontinuous (forget Λ X) (smallEtaleTopology X)

/-- The standard derived-category instance on `forget⁻¹ 𝒪_X`-modules. -/
instance underlineInverseImage_hasDerivedCategory :
    HasDerivedCategory (RingedSite.ModuleCat.{u + 1} (underlineInverseImageSite Λ X)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
    (underlineInverseImageSite Λ X)

/-- The standard derived-category instance on lifted `O`-modules on `C_{X/Λ}`. -/
instance structureModules_hasDerivedCategory :
    HasDerivedCategory
      (RingedSite.ModuleCat.{u + 1}
        (RingedSite.ofCommRingSheaf (topology Λ X) (structureSheafLift Λ X))) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
    (RingedSite.ofCommRingSheaf (topology Λ X) (structureSheafLift Λ X))

/-- The standard derived-category instance on lifted `underline{𝒪}_X`-modules on `C_{X/Λ}`. -/
instance underlineModules_hasDerivedCategory :
    HasDerivedCategory
      (RingedSite.ModuleCat.{u + 1}
        (RingedSite.ofCommRingSheaf (topology Λ X) (underlineSheafLift Λ X))) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
    (RingedSite.ofCommRingSheaf (topology Λ X) (underlineSheafLift Λ X))

/-- Module lower shriek along `forget` is additive. -/
instance forget_moduleLowerShriek_additive :
    (moduleLowerShriek (J := topology Λ X) (K := smallEtaleTopology X)
      (forget Λ X) (ringOf (commStructureSheafLift X))).Additive :=
  moduleLowerShriek.additive (J := topology Λ X) (K := smallEtaleTopology X)
    (forget Λ X) (ringOf (commStructureSheafLift X))

/-- Homotopy-to-derived presentation of `Lπ_!`, landing in `D(𝒪_X)`. -/
abbrev lowerShriekToDerived :
    HomotopyCategory (RingedSite.ModuleCat.{u + 1} (underlineInverseImageSite Λ X)) (up ℤ) ⥤
      DerivedCategory (CommModules X) :=
  (moduleLowerShriek (J := topology Λ X) (K := smallEtaleTopology X)
      (forget Λ X) (ringOf (commStructureSheafLift X))).mapHomotopyCategory
      (up ℤ) ⋙
    DerivedCategory.Qh

/-- Unfolding of `lowerShriekToDerived`. -/
theorem lowerShriekToDerived_eq :
    lowerShriekToDerived Λ X =
      (moduleLowerShriek (J := topology Λ X) (K := smallEtaleTopology X)
          (forget Λ X) (ringOf (commStructureSheafLift X))).mapHomotopyCategory
          (up ℤ) ⋙
        DerivedCategory.Qh :=
  rfl

/-- The homotopy presentation of `Lπ_!` admits a total left derived functor. -/
instance lowerShriekToDerived_hasLeftDerived :
    Functor.HasLeftDerivedFunctor (lowerShriekToDerived Λ X)
      (HomotopyCategory.quasiIso
        (RingedSite.ModuleCat.{u + 1} (underlineInverseImageSite Λ X)) (up ℤ)) :=
  sorry

/-- Derived lower shriek `Lπ_!` of `forget⁻¹ 𝒪_X`-modules on `C_{X/Λ}`, landing in
`D(𝒪_X)`. -/
abbrev lowerShriek :
    DerivedCategory (RingedSite.ModuleCat.{u + 1} (underlineInverseImageSite Λ X)) ⥤
      DerivedCategory (CommModules X) :=
  (lowerShriekToDerived Λ X).totalLeftDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (RingedSite.ModuleCat.{u + 1} (underlineInverseImageSite Λ X)) (up ℤ))

/-- Unfolding of `lowerShriek` as the total left derived functor of the homotopy
presentation. -/
theorem lowerShriek_eq :
    lowerShriek Λ X =
      (lowerShriekToDerived Λ X).totalLeftDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (RingedSite.ModuleCat.{u + 1} (underlineInverseImageSite Λ X)) (up ℤ)) :=
  rfl

/-- Derived inverse image `Li^*` along `i♯ : O ⟶ underline{𝒪}_X`. -/
abbrev derivedInverseImage :
    RingedSite.Hom.ModuleDerived.{u + 1}
        (RingedSite.ofCommRingSheaf (topology Λ X) (structureSheafLift Λ X)) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1}
        (RingedSite.ofCommRingSheaf (topology Λ X) (underlineSheafLift Λ X)) :=
  SheafOfModules.RingedSite.SameSite.pullbackDerived.{u + 1, u, u + 1, u + 1}
    (structureSheafMapLift Λ X)

/-- Unfolding of `derivedInverseImage` as same-site derived extension of scalars along `i♯`. -/
theorem derivedInverseImage_eq :
    derivedInverseImage Λ X =
      SheafOfModules.RingedSite.SameSite.pullbackDerived.{u + 1, u, u + 1, u + 1}
        (structureSheafMapLift Λ X) :=
  rfl

/-- Transport of derived `underline{𝒪}_X`-modules along the comparison with
`forget⁻¹ 𝒪_X`. -/
abbrev transportDerived :=
  RingedSite.SameSite.pullbackDerived.{u + 1, u, u + 1, u + 1} (underlineRingComparison Λ X)

/-- Unfolding of `transportDerived`. -/
theorem transportDerived_eq :
    transportDerived Λ X =
      RingedSite.SameSite.pullbackDerived.{u + 1, u, u + 1, u + 1}
        (underlineRingComparison Λ X) :=
  rfl

/-- `Ω_{O/underline{Λ}}` placed in degree zero in `D(O)`. -/
def singleOmega :
    RingedSite.Hom.ModuleDerived.{u + 1}
      (RingedSite.ofCommRingSheaf (topology Λ X) (structureSheafLift Λ X)) :=
  (DerivedCategory.singleFunctor
      (RingedSite.ModuleCat.{u + 1}
        (RingedSite.ofCommRingSheaf (topology Λ X) (structureSheafLift Λ X)))
      (0 : ℤ)).obj (omega Λ X)

/-- Unfolding of `singleOmega`. -/
theorem singleOmega_eq :
    singleOmega Λ X =
      (DerivedCategory.singleFunctor
          (RingedSite.ModuleCat.{u + 1}
            (RingedSite.ofCommRingSheaf (topology Λ X) (structureSheafLift Λ X)))
          (0 : ℤ)).obj (omega Λ X) :=
  rfl

/-- `Ω_{O/underline{Λ}} ⊗_O underline{𝒪}_X` placed in degree zero in `D(underline{𝒪}_X)`. -/
def singleOmegaTensor :
    RingedSite.Hom.ModuleDerived.{u + 1}
      (RingedSite.ofCommRingSheaf (topology Λ X) (underlineSheafLift Λ X)) :=
  (DerivedCategory.singleFunctor
      (RingedSite.ModuleCat.{u + 1}
        (RingedSite.ofCommRingSheaf (topology Λ X) (underlineSheafLift Λ X)))
      (0 : ℤ)).obj (omegaTensor Λ X)

/-- Unfolding of `singleOmegaTensor`. -/
theorem singleOmegaTensor_eq :
    singleOmegaTensor Λ X =
      (DerivedCategory.singleFunctor
          (RingedSite.ModuleCat.{u + 1}
            (RingedSite.ofCommRingSheaf (topology Λ X) (underlineSheafLift Λ X)))
          (0 : ℤ)).obj (omegaTensor Λ X) :=
  rfl

/-- `omegaTensorInverseImage` placed in degree zero in `D(forget⁻¹ 𝒪_X)`. -/
def singleOmegaTensorInverseImage :
    DerivedCategory (RingedSite.ModuleCat.{u + 1} (underlineInverseImageSite Λ X)) :=
  (DerivedCategory.singleFunctor
      (RingedSite.ModuleCat.{u + 1} (underlineInverseImageSite Λ X)) (0 : ℤ)).obj
    (omegaTensorInverseImage Λ X)

/-- Unfolding of `singleOmegaTensorInverseImage`. -/
theorem singleOmegaTensorInverseImage_eq :
    singleOmegaTensorInverseImage Λ X =
      (DerivedCategory.singleFunctor
          (RingedSite.ModuleCat.{u + 1} (underlineInverseImageSite Λ X)) (0 : ℤ)).obj
        (omegaTensorInverseImage Λ X) :=
  rfl

/-- Because `Ω_{O/underline{Λ}}` is a flat `O`-module,
`Li^* Ω_{O/underline{Λ}} = i^* Ω_{O/underline{Λ}} = Ω_{O/underline{Λ}} ⊗_O underline{𝒪}_X`
in `D(underline{𝒪}_X)`. -/
theorem derivedInverseImage_omega :
    IsIsomorphic ((derivedInverseImage Λ X).obj (singleOmega Λ X))
      (singleOmegaTensor Λ X) :=
  sorry

/-- `Lπ_!(Li^* Ω_{O/underline{Λ}}) = Lπ_!(Ω_{O/underline{Λ}} ⊗_O underline{𝒪}_X)` in
`D(𝒪_X)`. -/
theorem lowerShriek_derivedInverseImage :
    IsIsomorphic
      ((lowerShriek Λ X).obj
        ((transportDerived Λ X).obj ((derivedInverseImage Λ X).obj (singleOmega Λ X))))
      ((lowerShriek Λ X).obj (singleOmegaTensorInverseImage Λ X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
