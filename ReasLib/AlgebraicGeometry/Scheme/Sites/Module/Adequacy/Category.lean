/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AdequateCategory
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.AffineEvaluation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Sheafification
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Kernel
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Cokernel
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Extension
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Colimits
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.CategoryTheory.Adjunction.Exactness

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace SheafOfModules.Adeq

variable (S : Scheme.{u}) (τ : StandardTopology)

/-- The zero module sheaf is adequate. -/
theorem instContainsZero :
    ObjectProperty.ContainsZero
      (@SheafOfModules.IsAdequate S τ ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ)) := sorry

/-- Adequate module sheaves are closed under kernels in the ambient module category. -/
theorem instIsClosedUnderKernels :
    ObjectProperty.IsClosedUnderKernels
      (@SheafOfModules.IsAdequate S τ ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ)) := sorry

/-- Adequate module sheaves are closed under cokernels in the ambient module category. -/
theorem instIsClosedUnderCokernels :
    ObjectProperty.IsClosedUnderCokernels
      (@SheafOfModules.IsAdequate S τ ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ)) := sorry

/-- Adequate module sheaves are closed under finite products in the ambient module category. -/
theorem instIsClosedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts
      (@SheafOfModules.IsAdequate S τ ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ)) := sorry

/-- Adequate module sheaves on a big site form an abelian category. -/
noncomputable def instAbelian :
    Abelian
      (@SheafOfModules.Adeq S τ ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- The inclusion of adequate module sheaves into all module sheaves is exact. -/
theorem inclusionExact :
    exactFunctor
      (@SheafOfModules.Adeq S τ ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ))
      (RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S))
      (ObjectProperty.ι
        (@SheafOfModules.IsAdequate S τ ModuleValuedFunctor.tensorExtensionUnderlying
          (@affineEvaluationUnderlying S τ))) := sorry

/-- Adequacy is closed under short exact extensions. -/
theorem instIsClosedUnderExtensions :
    ObjectProperty.IsClosedUnderExtensions
      (@SheafOfModules.IsAdequate S τ ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ)) := sorry

/-- The category of adequate module sheaves has all small colimits. -/
theorem instHasColimits :
    HasColimits
      (@SheafOfModules.Adeq S τ ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ)) := sorry

/-- The inclusion of adequate module sheaves preserves all small colimits. -/
theorem inclusionPreservesColimits :
    PreservesColimits
      (ObjectProperty.ι
        (@SheafOfModules.IsAdequate S τ ModuleValuedFunctor.tensorExtensionUnderlying
          (@affineEvaluationUnderlying S τ))) := sorry

end SheafOfModules.Adeq
