/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import StacksCheckRecall

@[expose] public section

universe u v

open AlgebraicGeometry

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Remark 111.27.5: there is a continuous map `Proj 𝒜 ⟶ Spec (.of (𝒜 0))`,
the underlying space map of the canonical structure morphism `Proj.toSpecZero`. -/
@[stacks 02EA] #check
  (AlgebraicGeometry.Proj.toSpecZero_base_continuous (𝒜 := 𝒜) :
    Continuous ((AlgebraicGeometry.Proj.toSpecZero 𝒜).base))

#check (AlgebraicGeometry.Proj.toSpecZero 𝒜)

end
