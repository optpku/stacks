/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Module.CountablyGenerated.Operations
public import ReasLib.LinearAlgebra.UniversallyInjective
public import ReasLib.RingTheory.Finiteness.Projective.CountablyGenerated
public import ReasLib.RingTheory.Flatness.MittagLeffler.DirectSum

/-!
# Projectivity criteria for Mittag-Leffler modules

This file owns the projectivity characterization of flat Mittag-Leffler modules. The primary API
lives in `Module.Projective`, with closure facts in `Module.MittagLeffler`.
-/

@[expose] public section

universe u v w x

namespace Module.MittagLeffler

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Example 10.91.1 (2), tag `059R`: every projective module is Mittag-Leffler. -/
@[stacks 059R "(2)"]
instance ofProjective [Module.Projective R M] : Module.MittagLeffler R M := sorry

/-- Explicit-hypothesis form of the canonical Mittag-Leffler instance for projective modules. -/
@[stacks 059R "explicit projective module"]
theorem of_projective (hM : Module.Projective R M) : Module.MittagLeffler R M := sorry

/-- Example 10.91.1 (3), tag `059R`: every free module is Mittag-Leffler. -/
@[stacks 059R "(3)"]
theorem of_free (N : Type w) [AddCommGroup N] [Module R N] [Module.Free R N] :
    Module.MittagLeffler R N := sorry

end Module.MittagLeffler

namespace Module.Projective

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.93.1, tag `059X`: a countably generated flat Mittag-Leffler module is projective. -/
@[stacks 059X]
theorem of_flat_mittagLeffler (hflat : Module.Flat R M)
    (hML : Module.MittagLeffler R M) (hM : Module.CountablyGenerated R M) :
    Module.Projective R M := sorry

/-- Theorem 10.93.3, tag `059Z`: a module is projective exactly when it is flat,
Mittag-Leffler, and an internal direct sum of countably generated submodules. -/
@[stacks 059Z]
theorem iff_flat_mittagLeffler_directSum :
    Module.Projective R M ↔
      Module.Flat R M ∧ Module.MittagLeffler R M ∧
        Module.IsDirectSumOfCountablyGenerated R M := sorry

end Module.Projective

namespace LinearMap.UniversallyInjective

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Lemma 10.93.4, tag `05A0`: a universally injective submodule of a flat Mittag-Leffler module
is projective when it is a direct sum of countably generated submodules. -/
@[stacks 05A0]
theorem projective {f : M →ₗ[R] N}
    (hf : UniversallyInjective.{u, v, w, max u (max v w)} f)
    [Module.Flat R N] [Module.MittagLeffler R N]
    (hM : Module.IsDirectSumOfCountablyGenerated.{u, v, x} R M) :
    Module.Projective R M := sorry

end LinearMap.UniversallyInjective
