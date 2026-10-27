/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.RingedTopos
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Equivalence
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig.Module

/-- The restriction-of-scalars functor for the étale morphism over `Spec ℤ` is a right adjoint. -/
theorem specIntegerRestrictionScalars_rightAdjoint :
    (SheafOfModules.restrictScalars
      (ringedToposHom
        (𝟙 (Spec (CommRingCat.of ℤ)))).structureMap).IsRightAdjoint :=
  SheafOfModules.ChangeOfRings.restrictScalars_isRightAdjoint_of_isIso _

/-- The module pullback functor over `Spec ℤ`, using its explicit scalar restriction adjunction. -/
noncomputable def specIntegerModulePullback :
    SheafOfModules (StandardTopology.Big.liftedRingedSite .etale
      (Spec (CommRingCat.of ℤ))).structureSheaf ⥤
      SheafOfModules (Small.liftedRingedSite
        (Spec (CommRingCat.of ℤ))).structureSheaf :=
  @RingedSite.ToposHom.modulePullback
    (X := Small.liftedRingedSite (Spec (CommRingCat.of ℤ)))
    (Y := StandardTopology.Big.liftedRingedSite .etale (Spec (CommRingCat.of ℤ))) _ _
    (ringedToposHom (𝟙 (Spec (CommRingCat.of ℤ))))
    specIntegerRestrictionScalars_rightAdjoint

/-- The étale module pullback over `Spec ℤ` is additive. -/
instance specIntegerModulePullback.instAdditive : specIntegerModulePullback.Additive :=
  @Functor.instAdditiveComp _ _ _ _ _ _
    ((ringedToposHom (𝟙 (Spec (CommRingCat.of ℤ)))).toTopos.moduleInverseImage _)
    ((ringedToposHom (𝟙 (Spec (CommRingCat.of ℤ)))).toTopos.moduleInverseImage_additive _)
    _ _ _ _
    (@SheafOfModules.ChangeOfRings.extendScalars_additive _ _ _ _ _ _
      specIntegerRestrictionScalars_rightAdjoint)

/-- The étale module pullback over `Spec ℤ` does not preserve injective objects. -/
theorem specIntegerModulePullback_not_preservesInjective :
    ¬ (specIntegerModulePullback).PreservesInjectiveObjects := sorry

/-- The étale module pullback over `Spec ℤ` does not preserve all K-injective cochain
complexes. -/
theorem specIntegerModulePullback_not_preservesKInjective :
    ¬ ∀ I : CochainComplex
        (SheafOfModules.{1} (StandardTopology.Big.liftedRingedSite .etale
          (Spec (CommRingCat.of ℤ))).structureSheaf) ℤ,
      I.IsKInjective →
        CochainComplex.IsKInjective
          ((specIntegerModulePullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := sorry

end AlgebraicGeometry.Scheme.Etale.SmallToBig.Module

end
