/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Fppf.DerivedUniverseLift
public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel

/-!
# Affine restriction and derived sections of fppf modules

Ordinary restriction evaluates sheaf sections and need not preserve epimorphisms.
Its total right-derived functor is constructed on enlarged coefficients using
K-injective replacements. Exact coefficient enlargement first makes this
construction available for modules with smaller section carriers.

Restriction along arbitrary continuous functors of ringed sites is the natural
generalization of the affine inclusion treated here.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.AssociatedModule CategoryTheory
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- Restriction of an fppf `𝒪_X`-module along the affine inclusion, as a
presheaf of modules over the restricted structure sheaf. -/
def restrictToAffinePresheaf :
    fppfModules X ⥤
      PresheafOfModules ((affineInclusion X).op ⋙ (structureSheaf X).obj) :=
  SheafOfModules.forget (structureSheaf X) ⋙
    PresheafOfModules.pushforward₀ (affineInclusion X) (structureSheaf X).obj

/-- Objectwise, `restrictToAffinePresheaf` evaluates at an affine object `x` as
the fppf sections of the original module at `x.obj`. -/
theorem restrictToAffinePresheaf_obj (M : fppfModules X) (x : affineSite X) :
    ((restrictToAffinePresheaf X).obj M).obj (op x) =
      M.val.obj (op x.obj) :=
  rfl

/-- Restriction of fppf `𝒪_X`-modules to the chaotic affine site: precompose
along `affineInclusion`, universe-lift carriers and coefficients, and identify
the coefficient sheaf with `affineStructureSheaf`. -/
def restrictToAffineModules :
    fppfModules X ⥤ RingedSite.ModuleCat.{u + 1} (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X)) where
  obj M :=
    ⟨liftedModulePresheaf (affineToOver X) ((restrictToAffinePresheaf X).obj M),
      Presheaf.isSheaf_bot _⟩
  map f :=
    ⟨liftedModuleNatTrans (affineToOver X) ((restrictToAffinePresheaf X).map f)⟩
  map_id := by
    intro M
    ext U m
    rfl
  map_comp := by
    intro M N P f g
    ext U m
    rfl

/-- Sections of `restrictToAffineModules` at an affine object `x` are the
universe-lifted fppf sections at `x.obj`. -/
theorem restrictToAffineModules_obj (M : fppfModules X) (x : affineSite X) :
    ((restrictToAffineModules X).obj M).val.obj (op x) =
      (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).obj
        ((ModuleCat.uliftFunctor.{u + 1, u} _).obj (M.val.obj (op x.obj))) :=
  rfl

/-- The underlying module presheaf of `restrictToAffineModules` is the
universe lift of `restrictToAffinePresheaf`. -/
theorem restrictToAffineModules_val (M : fppfModules X) :
    ((restrictToAffineModules X).obj M).val =
      liftedModulePresheaf (affineToOver X) ((restrictToAffinePresheaf X).obj M) :=
  rfl

/-- Restriction of fppf modules to the chaotic affine site is additive. -/
instance restrictToAffineModules.instAdditive :
    (restrictToAffineModules X).Additive :=
  sorry

/-- Restriction of enlarged fppf modules to affine objects, using the identity
comparison of coefficient sections and the bottom-topology sheaf condition. -/
def restrictLiftedToAffineModules :
    RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X) ⥤
      RingedSite.ModuleCat.{u + 1}
        (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X)) where
  obj M :=
    ⟨(PresheafOfModules.restrictScalars (affineCoefficientPresheafIso X).hom).obj
        ((PresheafOfModules.pushforward₀ (affineInclusion X)
          (liftedFppfRingedSite X).structureSheaf.obj).obj M.val),
      Presheaf.isSheaf_bot _⟩
  map f :=
    ⟨(PresheafOfModules.restrictScalars (affineCoefficientPresheafIso X).hom).map
        ((PresheafOfModules.pushforward₀ (affineInclusion X)
          (liftedFppfRingedSite X).structureSheaf.obj).map f.val)⟩
  map_id := by
    intro M
    ext U m
    rfl
  map_comp := by
    intro M N P f g
    ext U m
    rfl

/-- Restriction of enlarged fppf module sections to affine objects is additive. -/
instance restrictLiftedToAffineModules.instAdditive :
    (restrictLiftedToAffineModules X).Additive := sorry

/-- Total right-derived affine restriction on enlarged fppf modules, computed
by the specified K-injective replacements on the large fppf site. -/
def restrictLiftedToAffineDerived :
    RingedSite.Hom.ModuleDerived.{u + 1} (liftedFppfRingedSite X) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1}
        (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X)) :=
  @Functor.KInjectiveModel.derived
    (RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X)) inferInstance
    (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1} (liftedFppfRingedSite X))
    (SheafOfModules.LargeSite.grothendieck (ringedSite X).siteTopology
      (liftedFppfRingedSite X).structureSheaf)
    (RingedSite.ModuleCat.{u + 1}
      (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X))) inferInstance
    (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1}
      (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X)))
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1} (liftedFppfRingedSite X))
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
      (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X)))
    (restrictLiftedToAffineModules X) _

/-- Derived affine restriction first enlarges coefficients exactly and then
computes right-derived sections on affine objects. -/
def restrictToAffineDerived :
    @DerivedCategory (fppfModules X) inferInstance (fppfModulesAbelian X) (@HasDerivedCategory.standard (fppfModules X) inferInstance (fppfModulesAbelian X)) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1}
        (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X)) :=
  fppfModuleUniverseLiftDerived X ⋙ restrictLiftedToAffineDerived X

/-- Derived affine restriction is the composite of exact coefficient enlargement
and total right-derived restriction on enlarged modules. -/
theorem restrictToAffineDerived_eq :
    restrictToAffineDerived X =
      fppfModuleUniverseLiftDerived X ⋙ restrictLiftedToAffineDerived X := rfl

end AlgebraicGeometry.GroupoidsOver
