/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Away.Module
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Algebra

/-!
# Base-ring modules on degree-zero homogeneous localizations

This leaf owns the canonical restriction of scalars from the base ring to the
degree-zero chart of a homogeneous localization away from one homogeneous element.
The construction is independent of any chosen scalar tower on the original module.
-/

@[expose] public section

noncomputable section

universe u v w z

namespace HomogeneousLocalization.Away.Module

variable {ι : Type u} [AddCommMonoid ι] [DecidableEq ι]
variable {R : Type v} {S : Type w} {M : Type z}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommMonoid M] [Module S M] [Module R M]
variable (𝒜 : ι → Submodule R S) (ℳ : ι → Submodule R M)
variable [GradedAlgebra 𝒜] [SetLike.GradedSMul 𝒜 ℳ]

/-- The degree-zero chart away from a homogeneous element carries the canonical
`R`-module structure obtained by restricting scalars along
`R →+* HomogeneousLocalization.Away 𝒜 (f : S)`. -/
@[stacks 07Z2 "base-ring module on a degree-zero homogeneous localization"]
noncomputable instance instModuleBase {d : ι} (f : 𝒜 d) :
    Module R (degreeZeroPart 𝒜 ℳ f) :=
  Module.compHom (degreeZeroPart 𝒜 ℳ f)
    (algebraMap R (HomogeneousLocalization.Away 𝒜 (f : S)))

end HomogeneousLocalization.Away.Module
