/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Basic
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Away.Module
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finiteness of degree-zero homogeneous localizations

This leaf owns the finite-generation theorem for the degree-zero homogeneous localization of a
graded module.  It is independent of Proj, sheafification, and a particular presentation by
homogeneous generators.
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

/-- If the graded algebra is finite type over its degree-zero part and the graded module is
finite, then its degree-zero homogeneous localization is finite over the localized base. -/
@[stacks 07Z2 "finite degree-zero homogeneous localization over the degree-zero base"]
theorem finite_of_finiteType_degreeZero [Algebra.FiniteType (𝒜 0) S] [Module.Finite S M]
    {d : ι} [DirectSum.Decomposition ℳ] (f : 𝒜 d) :
    Module.Finite (HomogeneousLocalization.Away 𝒜 (f : S)) (degreeZeroPart 𝒜 ℳ f) := sorry

/-- A finite-type graded algebra and a finite graded module have a finite degree-zero homogeneous
localization over the degree-zero homogeneous localization of the base. -/
@[stacks 07Z2 "finite degree-zero homogeneous localization"]
theorem finite_of_finiteType [Algebra.FiniteType R S] [Module.Finite S M] {d : ι}
    [DirectSum.Decomposition ℳ] (f : 𝒜 d) :
    Module.Finite (HomogeneousLocalization.Away 𝒜 (f : S)) (degreeZeroPart 𝒜 ℳ f) := sorry

end HomogeneousLocalization.Away.Module
