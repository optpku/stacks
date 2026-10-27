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

/- 27.9.0.1: the canonical degree-zero map is the actual fraction section construction. -/
@[stacks 0AG1] #check
  ((Proj.AssociatedModule.degreeZeroToGlobalSections 𝒜 ℳ).toAddMonoidHom :
    ℳ 0 →+ Γ(Proj.AssociatedModule.sheaf 𝒜 ℳ, ⊤))
