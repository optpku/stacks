/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.FiniteTotalDimension
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k (Rᵐᵒᵖ)] [IsFiniteGlobalDimensionRing (Rᵐᵒᵖ)]

/- Lemma 57.5.1: for an object `K` of the derived category of right `R`-modules,
finite total `k`-dimension of its cohomology is equivalent to compactness. -/
@[stacks 0FYA]
#check
  (@CategoryTheory.DerivedCategory.finiteTotalDimension_iff_isCompactObject
    k R _ _ _ _ _ :
    ∀ (K : DerivedCategory (ModuleCat (Rᵐᵒᵖ))),
      GradedObject.FiniteTotalDimension
          (fun i : ℤ ↦
            (ModuleCat.restrictScalars (algebraMap k (Rᵐᵒᵖ))).obj
              ((DerivedCategory.homologyFunctor (ModuleCat (Rᵐᵒᵖ)) i).obj K)) ↔
        IsCompactObject K)

end CategoryTheory.DerivedCategory
