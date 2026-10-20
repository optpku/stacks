/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.KInjective
import StacksCheckRecall

open CategoryTheory
open SheafOfModules.RingedSite.TensorWithObject

universe u

variable (X : AlgebraicGeometry.Scheme.{u})
variable (K : CochainComplex
  (AlgebraicGeometry.RingedSpace.Modules X.toRingedSpace) ℤ) [K.IsKInjective]
variable (n : ℤ)

/- 36.18.2.1: The degree-`n` cohomology of `endDGA K` is canonically the degree-`n`
self-Ext of `K` in the derived category of `𝒪_X`-modules. -/
@[stacks 09M6] #check
  (CategoryTheory.CochainComplex.Enriched.injectiveDerivedHomLinearEquiv K K K (𝟙 K) n :
    (endDGA K).homology n ≃ₗ[ℤ]
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj K) n)
