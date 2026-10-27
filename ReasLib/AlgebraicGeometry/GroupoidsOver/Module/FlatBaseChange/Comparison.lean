/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Fppf.DirectImageLift
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.Fppf
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.HigherDirectImage.FlatBaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.IsomorphismClasses

/-! # Étale and fppf direct-image comparison

The topology comparisons use explicit coefficient enlargement on both sites.
A general comparison for ringed sites with restriction-acyclicity hypotheses
would extend these algebraic-stack results.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Enlarged fppf modules have enough injectives by the large-site generator construction. -/
instance liftedFppfEnoughInjectives (X : GroupoidsOver S) :
    EnoughInjectives (RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X)) :=
  SheafOfModules.LargeSite.enoughInjectives (ringedSite X).siteTopology
    (liftedFppfRingedSite X).structureSheaf

/-- Enlarged étale modules have enough injectives by the large-site generator construction. -/
instance liftedEtaleEnoughInjectives (X : GroupoidsOver S) :
    EnoughInjectives (EtaleModulesLift X) :=
  SheafOfModules.LargeSite.enoughInjectives X.etaleTopology
    (commEtaleRingedSiteLift X).structureSheaf

/-- Restriction of enlarged fppf modules to the étale topology is additive. -/
instance liftedRestrictionAdditive (X : GroupoidsOver S) [AlgebraicStack X] :
    (AlgebraicStack.liftedFppfToEtale X).Additive where
  map_add := by
    intros
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictScalars
      (AlgebraicStack.liftedEtaleToFppfCoefficients X)).map_add

/-- Higher direct images of locally quasi-coherent modules with flat base
change along quasi-compact quasi-separated morphisms of algebraic stacks agree
in the étale and fppf topologies, after restriction to enlarged étale modules. -/
theorem higherDirectImage_etale_iso_fppf {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : LQCohFbc X) (i : ℕ) :
    IsIsomorphic
      ((AlgebraicStack.liftedFppfToEtale Y).obj
        ((fppfHigherDirectImageLiftFunctor f i).obj
          ((fppfModuleUniverseLift X).obj ((LQCohFbc.toFppf X).obj F))))
      (moduleHigherDirectImage f F.obj i) := sorry

/-- Total direct images of locally quasi-coherent modules with flat base
change along quasi-compact quasi-separated morphisms of algebraic stacks agree
after derived restriction from fppf to étale modules with enlarged coefficients. -/
theorem derivedPushforward_etale_iso_fppf {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : LQCohFbc X) :
    IsIsomorphic
      (DerivedCategory.Plus.ι.obj
        ((AlgebraicStack.liftedFppfToEtale Y).rightDerivedFunctorPlus.obj
          ((fppfDerivedDirectImageLiftFunctor f).obj
            ((DerivedCategory.Plus.singleFunctor
              (RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X)) (0 : ℤ)).obj
                ((fppfModuleUniverseLift X).obj ((LQCohFbc.toFppf X).obj F))))))
      (DerivedCategory.Plus.ι.obj
        ((etaleDerivedDirectImageLiftFunctor f).obj
          ((DerivedCategory.Plus.singleFunctor (EtaleModulesLift X) (0 : ℤ)).obj
            ((ModuleUniverseComparison.lift X).obj F.obj)))) := sorry

/-- Enlarged étale higher direct images along quasi-compact quasi-separated
morphisms of algebraic stacks remain locally quasi-coherent with flat base change. -/
theorem mem_lqcohFbc_higherDirectImage {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : LQCohFbc X) (i : ℕ) :
    AlgebraicStack.liftedEtaleLqcohFbc Y (moduleHigherDirectImage f F.obj i) :=
  ⟨AlgebraicStack.isLocallyQuasiCoherent_higherDirectImage_of f
      ((lqcohFbc_iff _).mp F.property).1 i,
    @AlgebraicStack.hasFlatBaseChange_higherDirectImage S X Y _ _ f _ _ F.obj
      ((lqcohFbc_iff _).mp F.property).1 ((lqcohFbc_iff _).mp F.property).2 i⟩

end AlgebraicGeometry.GroupoidsOver
