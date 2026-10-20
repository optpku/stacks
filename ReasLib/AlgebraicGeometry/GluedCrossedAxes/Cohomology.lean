/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.GluedCrossedAxes.Gluing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Cohomology of glued crossed axes

The degree-one cohomology of the structure sheaf is finite-dimensional of
rank one over the field, using scalars induced by the structure morphism.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GluedCrossedAxes

/-- Degree-one cohomology of `𝒪_X` is finite-dimensional over `k`. -/
instance finiteDimensional_structureSheaf_cohomology_one (k : Type u) [Field k] :
    FiniteDimensional k
      (Scheme.Hom.cohomology (toBase k)
        (SheafOfModules.unit (scheme k).ringCatSheaf : (scheme k).Modules) 1) := sorry

/-- `dim H¹(X, 𝒪_X) = 1`. -/
theorem structureSheaf_cohomologyFinrank_one (k : Type u) [Field k] :
    Scheme.Hom.cohomologyFinrank (toBase k)
      (SheafOfModules.unit (scheme k).ringCatSheaf : (scheme k).Modules) 1 = 1 := sorry

end AlgebraicGeometry.GluedCrossedAxes
