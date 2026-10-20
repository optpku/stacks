/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Ideals Acting on Submodules

This leaf records small comparison lemmas between an ideal action in an
ambient module and the induced action inside a submodule.
-/

@[expose] public section

universe u v

namespace Submodule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Viewing `J • N` as a submodule of `N` agrees with the intrinsic ideal
multiple `J • ⊤` in `N`. -/
theorem submoduleOf_ideal_smul (J : Ideal R) (N : Submodule R M) :
    (J • N).submoduleOf N = J • (⊤ : Submodule R N) := sorry

end Submodule
