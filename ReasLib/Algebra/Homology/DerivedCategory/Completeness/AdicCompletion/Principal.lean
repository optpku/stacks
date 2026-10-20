/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.RingTheory.Ideal.Principal.PowerIntersection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal derived completeness and completion kernels

For a module derived complete with respect to `(f)`, the intersection of the powers of `(f)`
annihilates the kernel of the ordinary completion map. Applied to the ring itself, this makes the
power intersection square-zero.

@stack 0G3G
-/

@[expose] public section

universe u

namespace ModuleCat.IsDerivedCompleteWithRespectTo

variable {A : Type u} [CommRing A]

/-- Lemma 15.94.9 (1) (Stacks `0G3G`): if an `A`-module `M` is derived complete with respect to
`(f)`, then `⋂ n, (f)^n` annihilates the kernel of the ordinary `(f)`-adic completion map. -/
@[stacks 0G3G "(1), principal-power intersection annihilates the completion kernel"]
theorem principalPowerIntersection_smul_completionKer_eq_bot
    (f : A) (M : ModuleCat.{u, u} A)
    (hM : M.IsDerivedCompleteWithRespectTo (principalIdeal f)) :
    Ideal.principalPowerIntersection f •
        LinearMap.ker (AdicCompletion.of (principalIdeal f) M) = ⊥ := sorry

/-- Lemma 15.94.9 (2) (Stacks `0G3G`): if `A`, viewed as an `A`-module, is derived complete with
respect to `(f)`, then the intersection of the powers of `(f)` is square-zero. -/
@[stacks 0G3G "(2), square-zero principal-power intersection"]
theorem principalPowerIntersection_sq_eq_bot
    (f : A)
    (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo (principalIdeal f)) :
    (Ideal.principalPowerIntersection f) ^ 2 = ⊥ := sorry

end ModuleCat.IsDerivedCompleteWithRespectTo
