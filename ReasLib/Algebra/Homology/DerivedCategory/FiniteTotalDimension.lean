/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.GradedObject.Duality
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Compact
public import ReasLib.RingTheory.GlobalDimension.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k (Rᵐᵒᵖ)] [IsFiniteGlobalDimensionRing (Rᵐᵒᵖ)]

/-- For a finite-dimensional finite-global-dimension algebra, finite total homology dimension is
equivalent to compactness in the derived category of right modules. -/
theorem finiteTotalDimension_iff_isCompactObject
    (K : DerivedCategory (ModuleCat (Rᵐᵒᵖ))) :
    GradedObject.FiniteTotalDimension
        (fun i : ℤ ↦
          (ModuleCat.restrictScalars (algebraMap k (Rᵐᵒᵖ))).obj
            ((DerivedCategory.homologyFunctor (ModuleCat (Rᵐᵒᵖ)) i).obj K)) ↔
      IsCompactObject K := sorry

end CategoryTheory.DerivedCategory
