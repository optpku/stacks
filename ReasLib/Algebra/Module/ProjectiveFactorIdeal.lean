/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Operations
public import ReasLib.LinearAlgebra.LinearMap.Factorisation.Projective

@[expose] public section

/-!
# Projective-factor ideals

For an `R`-module `M`, the scalars whose action on `M` factors through a projective module form
an ideal of `R`.  This ideal is the canonical owner of ideal-projectivity: an ideal `I` makes `M`
ideal-projective precisely when `I` is contained in it.

The ideal-valued API records more information than the original pointwise predicate and makes
monotonicity, comparison, annihilator, and duality results ordinary ideal inclusions.

@stack 0G93
-/

universe u v

namespace Module

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- The ideal of scalars whose action on `M` factors through a projective module. -/
@[stacks 0G93 "projective-factor ideal"]
def projectiveFactorIdeal (R : Type u) (M : Type v) [CommSemiring R]
    [AddCommMonoid M] [Module R M] : Ideal R :=
  (LinearMap.projectiveFactors (R := R) (M := M) (N := M)).comap (LinearMap.lsmul R M)

/-- Membership in `projectiveFactorIdeal` is projective factorisation of the scalar action. -/
theorem mem_projectiveFactorIdeal (a : R) :
    a ∈ projectiveFactorIdeal R M ↔
      (LinearMap.lsmul R M a).FactorsThroughProjective := by
  change (LinearMap.lsmul R M a) ∈
      LinearMap.projectiveFactors (R := R) (M := M) (N := M) ↔ _
  rfl

/-- An ideal `I` makes `M` ideal-projective when all its scalar actions factor through
projective modules. -/
@[stacks 0G93 "ideal-projective module"]
def IsIdealProjective (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] : Prop :=
  I ≤ projectiveFactorIdeal R M

/-- The pointwise factorisation criterion for ideal-projectivity. -/
theorem isIdealProjective_iff (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] :
    IsIdealProjective I M ↔
      ∀ a : I, (LinearMap.lsmul R M (a : R)).FactorsThroughProjective := by
  constructor
  · intro h a
    exact (mem_projectiveFactorIdeal (R := R) (M := M) (a : R)).mp (h a.2)
  · intro h a ha
    exact (mem_projectiveFactorIdeal (R := R) (M := M) a).mpr (h ⟨a, ha⟩)

namespace IsIdealProjective

variable {I J : Ideal R}

/-- An ideal-projectivity hypothesis gives membership in the projective-factor ideal. -/
theorem mem_projectiveFactorIdeal (h : IsIdealProjective I M) {a : R} (ha : a ∈ I) :
    a ∈ projectiveFactorIdeal R M := h ha

/-- An ideal-projectivity hypothesis gives the structured projective factorisation of each
scalar action. -/
theorem factorisation (h : IsIdealProjective I M) (a : I) :
    Nonempty (LinearMap.Factorisation.Projective (LinearMap.lsmul R M (a : R))) :=
  (Module.mem_projectiveFactorIdeal (R := R) (M := M) (a : R)).mp
    (h a.2)

/-- Compatibility view of an ideal-projectivity hypothesis as an explicit projective
factorisation.  New code should normally use `factorisation` or ideal membership instead. -/
theorem factorsThroughProjective (h : IsIdealProjective I M) (a : I) :
    ∃ (P : Type (max u v)) (_ : AddCommMonoid P) (_ : Module R P)
      (_ : Module.Projective R P) (i : M →ₗ[R] P) (r : P →ₗ[R] M),
      LinearMap.lsmul R M (a : R) = r.comp i := by
  rcases h.factorisation a with ⟨F⟩
  refine ⟨F.mid, inferInstance, inferInstance, F.projective, F.fromSource, F.toTarget, ?_⟩
  exact F.base.factor.symm

/-- Ideal-projectivity is contravariantly monotone in the ideal. -/
theorem mono (h : IsIdealProjective I M) (hJI : J ≤ I) : IsIdealProjective J M := by
  intro a ha
  exact h (hJI ha)

/-- Every module is ideal-projective for the zero ideal. -/
theorem zero (M : Type v) [AddCommMonoid M] [Module R M] :
    IsIdealProjective (⊥ : Ideal R) M := bot_le

/-- A projective module is ideal-projective for every ideal. -/
theorem of_projective (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M]
    [Module.Projective R M] : IsIdealProjective I M := by
  intro a ha
  apply (Module.mem_projectiveFactorIdeal (R := R) (M := M) a).mpr
  let e : ULift.{u} M ≃ₗ[R] M := ULift.moduleEquiv
  refine ⟨LinearMap.Factorisation.Projective.ofMaps (ULift.{u} M)
    e.symm.toLinearMap ((LinearMap.lsmul R M a).comp e.toLinearMap) ?_⟩
  ext x
  simp

/-- Projectivity is the top-ideal case of ideal-projectivity. -/
theorem top_iff (M : Type v) [AddCommMonoid M] [Module R M] :
    IsIdealProjective (⊤ : Ideal R) M ↔ Module.Projective R M := by
  constructor
  · intro h
    rcases h.factorisation ⟨1, Submodule.mem_top⟩ with ⟨F⟩
    let e : LinearMap.lsmul R M 1 = LinearMap.id := by
      ext x
      simp [LinearMap.lsmul_apply]
    letI : Module.Projective R F.mid := F.projective
    apply Module.Projective.of_split F.fromSource F.toTarget
    exact F.base.factor.trans e
  · intro h
    exact of_projective (⊤ : Ideal R) M

end IsIdealProjective

namespace projectiveFactorIdeal

/-- The projective-factor ideal is the top ideal exactly for projective modules. -/
@[stacks 0G93 "projectivity detected by the projective-factor ideal"]
theorem eq_top_iff (M : Type v) [AddCommMonoid M] [Module R M] :
    projectiveFactorIdeal R M = ⊤ ↔ Module.Projective R M := by
  constructor
  · intro h
    apply (IsIdealProjective.top_iff (R := R) M).mp
    intro a ha
    simpa [h]
  · intro h
    apply top_unique
    intro a ha
    exact (IsIdealProjective.top_iff (R := R) M).mpr h ha

end projectiveFactorIdeal

end Module
