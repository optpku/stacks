/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Naturality
public import stacks_project.Chap85.Lemma_85_33_4_Sections
public import stacks_project.Chap85.Lemma_85_34_4_Equivalence

/-!
# Derived global-sections comparison for an fppf hypercovering of modules

If `a : U ⟶ X` is an augmentation of algebraic spaces, derived global sections of
`𝒪_X`-modules identify after `Ra_*` with derived global sections on `U_étale`.
The canonical comparison `RΓ(X_étale, -) ⟶ a^* ⋙ RΓ(U_étale, -)` is the derived
unit of `a^* ⊣ Ra_*` followed by that Leray identification, on the Section 85.32
spaces-étale ringed sites at coefficient universe `u + 1`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Functor ComplexShape
open RingedSite.Hom
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

-- Local instance justification (defeq pin): `Hom.moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `Hom.ModuleDerived`, `Qh`, and `totalRightDerived` of module global sections must share that same derived-category instance.
attribute [local instance] moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): `mapHomotopyCategory` of `moduleGlobalSectionsAdditiveFunctor` in `rGammaPushforwardHomotopyIso` must use the named additive structure of that functor, not a freshly synthesized `Functor.Additive`.
attribute [local instance] moduleGlobalSectionsAdditiveFunctor_additive
-- Local instance justification (defeq pin): `totalRightDerivedUnit` of `moduleGlobalSectionsToDerived` must use the named `HasRightDerivedFunctor` instance that defines `moduleGlobalSectionsDerived`.
attribute [local instance] moduleGlobalSectionsToDerived_hasRightDerivedFunctor

variable {S : Scheme.{u}}

/-- Module sheaves on `X_spaces,étale` at coefficient universe `u + 1` form a
Grothendieck abelian category. -/
instance isGrothendieckAbelian_moduleCat_spacesRingedSite (X : AlgebraicSpace S) :
    IsGrothendieckAbelian.{u + 1} (RingedSite.ModuleCat.{u + 1} (spacesRingedSite X)) :=
  sorry

/-- Module sheaves on `U_spaces,étale` at coefficient universe `u + 1` form a
Grothendieck abelian category. -/
instance isGrothendieckAbelian_moduleCat_etaleTotalRingedSite
    (U : SimplicialObject (AlgebraicSpace S)) :
    IsGrothendieckAbelian.{u + 1} (RingedSite.ModuleCat.{u + 1} (etaleTotalRingedSite U)) :=
  sorry

variable {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- The underived additive comparison `Γ(U_étale, -) ⟶ a_* ⋙ Γ(X_étale, -)` is an
isomorphism. -/
instance moduleGlobalSectionsPushforwardNat_isIso :
    IsIso (ModuleSections.pushforwardNat.{u + 1} (spacesEtaleAugmentationHom a)) :=
  sorry

/-- Underived identification `a_* ⋙ Γ(X_étale, -) ≅ Γ(U_étale, -)` after forgetting
to `Ab`. -/
def directImageCompGlobalSectionsIso :
    (spacesEtaleAugmentationHom a).modulePushforward.{u + 1} ⋙
      moduleGlobalSectionsAdditiveFunctor.{u + 1} (spacesRingedSite X) ≅
    moduleGlobalSectionsAdditiveFunctor.{u + 1} (etaleTotalRingedSite U) :=
  (asIso (ModuleSections.pushforwardNat.{u + 1} (spacesEtaleAugmentationHom a))).symm

/-- `directImageCompGlobalSectionsIso` is the inverse of the additive
`ModuleSections.pushforwardNat` comparison. -/
theorem directImageCompGlobalSectionsIso_eq :
    directImageCompGlobalSectionsIso a =
      (asIso (ModuleSections.pushforwardNat.{u + 1} (spacesEtaleAugmentationHom a))).symm :=
  sorry

/-- Homotopy-level identification of `a_* ⋙ Γ(X_étale, -)` with `Γ(U_étale, -)`. -/
def rGammaPushforwardHomotopyIso :
    (spacesEtaleAugmentationHom a).modulePushforward.{u + 1}.mapHomotopyCategory (up ℤ) ⋙
      moduleGlobalSectionsToDerived.{u + 1} (spacesRingedSite X) ≅
    moduleGlobalSectionsToDerived.{u + 1} (etaleTotalRingedSite U) :=
  (associator
      ((spacesEtaleAugmentationHom a).modulePushforward.{u + 1}.mapHomotopyCategory (up ℤ))
      ((moduleGlobalSectionsAdditiveFunctor.{u + 1} (spacesRingedSite X)).mapHomotopyCategory
        (up ℤ))
      DerivedCategory.Qh).symm ≪≫
    isoWhiskerRight
      (mapHomotopyCategoryCompIso (directImageCompGlobalSectionsIso a) (up ℤ))
      DerivedCategory.Qh

/-- The iterated unit exhibiting `Ra_* ⋙ RΓ(X_étale, -)` as a right-derived model of
`a_* ⋙ Γ(X_étale, -)`. -/
def rGammaPushforwardUnit :
    (spacesEtaleAugmentationHom a).modulePushforward.{u + 1}.mapHomotopyCategory (up ℤ) ⋙
      moduleGlobalSectionsToDerived.{u + 1} (spacesRingedSite X) ⟶
    moduleLocalization.{u + 1} (etaleTotalRingedSite U) ⋙
      modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a) ⋙
        moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X) :=
  whiskerLeft
      ((spacesEtaleAugmentationHom a).modulePushforward.{u + 1}.mapHomotopyCategory (up ℤ))
      (totalRightDerivedUnit
        (moduleGlobalSectionsToDerived.{u + 1} (spacesRingedSite X))
        (moduleLocalization.{u + 1} (spacesRingedSite X))
        (ModuleQis.{u + 1} (spacesRingedSite X))) ≫
    (associator
        ((spacesEtaleAugmentationHom a).modulePushforward.{u + 1}.mapHomotopyCategory (up ℤ))
        (moduleLocalization.{u + 1} (spacesRingedSite X))
        (moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X))).inv ≫
    whiskerRight
      (totalRightDerivedUnit
        (modulePushforwardToDerived.{u + 1} (spacesEtaleAugmentationHom a))
        (moduleLocalization.{u + 1} (etaleTotalRingedSite U))
        (ModuleQis.{u + 1} (etaleTotalRingedSite U)))
      (moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X)) ≫
    (associator (moduleLocalization.{u + 1} (etaleTotalRingedSite U))
        (modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a))
        (moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X))).hom

/-- The iterated model `Ra_* ⋙ RΓ(X_étale, -)` is a right-derived functor of
`a_* ⋙ Γ(X_étale, -)`. -/
instance rGammaPushforward_isRightDerived :
    (modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a) ⋙
        moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X)).IsRightDerivedFunctor
      (rGammaPushforwardUnit a) (ModuleQis.{u + 1} (etaleTotalRingedSite U)) :=
  sorry

/-- Leray identification `Ra_* ⋙ RΓ(X_étale, -) ≅ RΓ(U_étale, -)` in `D(Ab)`. -/
def rGammaPushforwardIso :
    modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a) ⋙
      moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X) ≅
    moduleGlobalSectionsDerived.{u + 1} (etaleTotalRingedSite U) :=
  rightDerivedNatIso
    (modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a) ⋙
      moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X))
    (moduleGlobalSectionsDerived.{u + 1} (etaleTotalRingedSite U))
    (rGammaPushforwardUnit a)
    (totalRightDerivedUnit
      (moduleGlobalSectionsToDerived.{u + 1} (etaleTotalRingedSite U))
      (moduleLocalization.{u + 1} (etaleTotalRingedSite U))
      (ModuleQis.{u + 1} (etaleTotalRingedSite U)))
    (ModuleQis.{u + 1} (etaleTotalRingedSite U))
    (rGammaPushforwardHomotopyIso a)

/-- `rGammaPushforwardIso` is `rightDerivedNatIso` of `rGammaPushforwardHomotopyIso`. -/
theorem rGammaPushforwardIso_eq :
    rGammaPushforwardIso a =
      rightDerivedNatIso
        (modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a) ⋙
          moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X))
        (moduleGlobalSectionsDerived.{u + 1} (etaleTotalRingedSite U))
        (rGammaPushforwardUnit a)
        (totalRightDerivedUnit
          (moduleGlobalSectionsToDerived.{u + 1} (etaleTotalRingedSite U))
          (moduleLocalization.{u + 1} (etaleTotalRingedSite U))
          (ModuleQis.{u + 1} (etaleTotalRingedSite U)))
        (ModuleQis.{u + 1} (etaleTotalRingedSite U))
        (rGammaPushforwardHomotopyIso a) :=
  sorry

/-- Canonical Leray comparison `Ra_* ⋙ RΓ(X_étale, -) ⟶ RΓ(U_étale, -)`. -/
def rGammaPushforwardComparison :
    modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a) ⋙
      moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X) ⟶
    moduleGlobalSectionsDerived.{u + 1} (etaleTotalRingedSite U) :=
  (rGammaPushforwardIso a).hom

/-- `rGammaPushforwardComparison` is the forward map of `rGammaPushforwardIso`. -/
theorem rGammaPushforwardComparison_eq :
    rGammaPushforwardComparison a = (rGammaPushforwardIso a).hom :=
  sorry

/-- Canonical comparison `RΓ(X_étale, -) ⟶ a^* ⋙ RΓ(U_étale, -)`. -/
def rGammaPullbackComparison :
    moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X) ⟶
      modulePullbackDerived.{u + 1} (spacesEtaleAugmentationHom a) ⋙
        moduleGlobalSectionsDerived.{u + 1} (etaleTotalRingedSite U) :=
  whiskerRight (derivedModuleAdjunction a).unit
      (moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X)) ≫
    (associator
        (modulePullbackDerived.{u + 1} (spacesEtaleAugmentationHom a))
        (modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a))
        (moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X))).hom ≫
    whiskerLeft (modulePullbackDerived.{u + 1} (spacesEtaleAugmentationHom a))
      (rGammaPushforwardIso a).hom

/-- `rGammaPullbackComparison` is the derived unit of `a^* ⊣ Ra_*`, reassociated and
postcomposed with the Leray identification `rGammaPushforwardIso`. -/
theorem rGammaPullbackComparison_eq :
    rGammaPullbackComparison a =
      whiskerRight (derivedModuleAdjunction a).unit
          (moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X)) ≫
        (associator
            (modulePullbackDerived.{u + 1} (spacesEtaleAugmentationHom a))
            (modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a))
            (moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X))).hom ≫
        whiskerLeft (modulePullbackDerived.{u + 1} (spacesEtaleAugmentationHom a))
          (rGammaPushforwardIso a).hom :=
  sorry

/-- The component of `rGammaPullbackComparison` at `K` is
`RΓ(X_étale, K) ⟶ RΓ(U_étale, a^* K)`. -/
theorem rGammaPullbackComparison_app
    (K : ModuleDerived.{u + 1} (spacesRingedSite X)) :
    (rGammaPullbackComparison a).app K =
      (moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite X)).map
          ((derivedModuleAdjunction a).unit.app K) ≫
        (rGammaPushforwardIso a).hom.app
          ((modulePullbackDerived.{u + 1} (spacesEtaleAugmentationHom a)).obj K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
