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

variable (n : ℤ)

/- 27.9.0.2: use the actual translated grading and its canonical fraction section map. -/
@[stacks 0AG2] #check
  (Proj.AssociatedModule.ShiftedSections.sectionMap 𝒜 ℳ n :
    ℳ n →+ Γ(Proj.AssociatedModule.sheaf 𝒜 (GradedModule.shiftGrading ℳ n), ⊤))
