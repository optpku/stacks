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

variable (hcover : Proj.degreeOpen 𝒜 1 = ⊤)

/- 27.10.3.2: the canonical graded map to the actual tensor twists under the degree-one cover. -/
@[stacks 0AG4] #check
  (Proj.AssociatedModule.ShiftedSections.tensorGradedMap 𝒜 ℳ hcover :
    (⨁ n : ℤ, ℳ n) →ₗ[(⨁ d : ℕ, 𝒜 d)]
      (⨁ n : ℤ, Proj.AssociatedModule.ShiftedSections.tensorDegree 𝒜 ℳ n))
