/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Ringed

/-!
# Abelian categories of modules on algebraic-stack sites

Sheaves of modules on arbitrary sites already form abelian categories under
appropriate sheafification or universe-bounding conditions. The lisse-étale
and flat-fppf module categories below use the smaller coefficient universe,
without assuming those bounds. Finite limits come from the arbitrary-site
construction; normality and cokernel existence supply the remaining properties.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Every monomorphism of lisse-étale modules on an algebraic stack is normal. -/
instance lisseEtaleModules_isNormalMonoCategory (X : GroupoidsOver S) [AlgebraicStack X] :
    IsNormalMonoCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) :=
  sorry

/-- Every epimorphism of lisse-étale modules on an algebraic stack is normal. -/
instance lisseEtaleModules_isNormalEpiCategory (X : GroupoidsOver S) [AlgebraicStack X] :
    IsNormalEpiCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) :=
  sorry

/-- The category of lisse-étale modules on an algebraic stack has cokernels. -/
instance lisseEtaleModules_hasCokernels (X : GroupoidsOver S) [AlgebraicStack X] :
    HasCokernels (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) :=
  sorry

/-- The category of lisse-étale `𝒪`-modules on an algebraic stack is abelian. -/
instance lisseEtaleModules_abelian (X : GroupoidsOver S) [AlgebraicStack X] :
    Abelian (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := lisseEtaleModules_isNormalMonoCategory X
  toIsNormalEpiCategory := lisseEtaleModules_isNormalEpiCategory X
  has_finite_products := inferInstance
  has_kernels := inferInstance
  has_cokernels := lisseEtaleModules_hasCokernels X

/-- Every monomorphism of flat-fppf modules on an algebraic stack is normal. -/
instance flatFppfModules_isNormalMonoCategory (X : GroupoidsOver S) [AlgebraicStack X] :
    IsNormalMonoCategory (SheafOfModules.{u} (flatFppfStructureSheaf X)) :=
  sorry

/-- Every epimorphism of flat-fppf modules on an algebraic stack is normal. -/
instance flatFppfModules_isNormalEpiCategory (X : GroupoidsOver S) [AlgebraicStack X] :
    IsNormalEpiCategory (SheafOfModules.{u} (flatFppfStructureSheaf X)) :=
  sorry

/-- The category of flat-fppf modules on an algebraic stack has cokernels. -/
instance flatFppfModules_hasCokernels (X : GroupoidsOver S) [AlgebraicStack X] :
    HasCokernels (SheafOfModules.{u} (flatFppfStructureSheaf X)) :=
  sorry

/-- The category of flat-fppf `𝒪`-modules on an algebraic stack is abelian. -/
instance flatFppfModules_abelian (X : GroupoidsOver S) [AlgebraicStack X] :
    Abelian (SheafOfModules.{u} (flatFppfStructureSheaf X)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := flatFppfModules_isNormalMonoCategory X
  toIsNormalEpiCategory := flatFppfModules_isNormalEpiCategory X
  has_finite_products := inferInstance
  has_kernels := inferInstance
  has_cokernels := flatFppfModules_hasCokernels X

end AlgebraicGeometry.AlgebraicStack
