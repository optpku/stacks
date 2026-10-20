/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.ContentIdeal
public import ReasLib.LinearAlgebra.UniversallyInjective.Quotient
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Content ideals and injective module maps

Tensor-stable injectivity preserves content ideals. Criteria that produce the
required quotient injectivity live in subordinate leaves.

@stack 0ASC
-/

universe u v w

namespace IsContentIdeal

section UniversallyInjective

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]
variable {x : M} {I : Ideal A}

/-- Content ideals are preserved by universally injective linear maps. -/
@[stacks 0ASC "content ideals under universally injective maps"]
theorem map_of_universallyInjective (hI : IsContentIdeal x I)
    (f : M →ₗ[A] N)
    (hf : LinearMap.UniversallyInjective.{u, v, w, max u v w} f) :
    IsContentIdeal (f x) I := sorry
-- Proof strategy: map `hI.mem` using `Submodule.map_smul''`; for minimality, apply
-- `LinearMap.injective_quotientMapByIdeal_of_universallyInjective` at an arbitrary ideal `J`,
-- reflect vanishing of the class of `f x`, and conclude with `hI.le`.

end UniversallyInjective

end IsContentIdeal
