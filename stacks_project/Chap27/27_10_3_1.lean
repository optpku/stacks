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

variable (hcover : Proj.degreeOpen 𝒜 1 = ⊤) (n : ℤ)

/- 27.10.3.1: under the degree-one standard-open cover, the canonical section lands in
`M̃ ⊗ 𝒪(n)`, using the local formula `(m/f^n) ⊗ f^n`. -/
@[stacks 0AG3] #check
  (Proj.AssociatedModule.ShiftedSections.tensorSectionMap 𝒜 ℳ hcover n :
    ℳ n →+ Γ(Proj.AssociatedModule.ShiftedSections.tensorTwistSheaf 𝒜 ℳ n, ⊤))
