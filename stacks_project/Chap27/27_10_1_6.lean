/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.EventualSections
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]

variable [DirectSum.Decomposition ℳ]

/- 27.10.1.6: the canonical graded map to sections of the actual shifted associated sheaves.
The source grading and canonical homogeneous multiplication determine both actions. -/
@[stacks 01MR] #check
  (gradedModuleToProjAssociatedTwistGlobalSectionsMap 𝒜 ℳ :
    (⨁ n : ℤ, ℳ n) →ₗ[(⨁ d : ℕ, 𝒜 d)]
      (⨁ n : ℤ, Γ(projAssociatedTwist 𝒜 ℳ n, ⊤)))
