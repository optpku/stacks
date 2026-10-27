/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Fppf.DirectImageLift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived enlargement of fppf module coefficients

Enlarging both coefficients and section carriers is exact, and therefore acts
on unbounded derived categories using their standard presentations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- Enlargement of fppf coefficients and section carriers is additive. -/
instance fppfModuleUniverseLift.instAdditive :
    (fppfModuleUniverseLift X).Additive := sorry

/-- Enlargement of fppf coefficients and section carriers preserves finite limits. -/
instance fppfModuleUniverseLift.preservesFiniteLimits :
    PreservesFiniteLimits (fppfModuleUniverseLift X) := sorry

/-- Enlargement of fppf coefficients and section carriers preserves finite colimits. -/
instance fppfModuleUniverseLift.preservesFiniteColimits :
    PreservesFiniteColimits (fppfModuleUniverseLift X) := sorry

/-- Exact coefficient enlargement on the unbounded derived category of fppf modules. -/
def fppfModuleUniverseLiftDerived :
    @DerivedCategory (fppfModules X) inferInstance (fppfModulesAbelian X)
      (@HasDerivedCategory.standard (fppfModules X) inferInstance (fppfModulesAbelian X)) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1} (liftedFppfRingedSite X) :=
  @Functor.mapDerivedCategory
    (fppfModules X) inferInstance (fppfModulesAbelian X)
      (@HasDerivedCategory.standard (fppfModules X) inferInstance (fppfModulesAbelian X))
    (RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X)) inferInstance
    (RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u + 1} (liftedFppfRingedSite X))
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1} (liftedFppfRingedSite X))
    (fppfModuleUniverseLift X) _ _ _

end AlgebraicGeometry.GroupoidsOver
