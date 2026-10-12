/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical localized submodule order and images

This leaf records model-free order and image consequences for canonical
submodule localization. It packages the frequent situations where one
localized scalar gives an inclusion or a submodule becomes all of the
localized source module.

@stack 00DV
@stack 05N6
-/

@[expose] public section

universe u v w

namespace Submodule

open scoped Pointwise

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/- The canonical `localized` API hides the chosen `Localization S` model. -/

/-- A scalar from the localizing submonoid that sends `P` into `Q` gives the corresponding
inclusion after canonical localization. -/
@[stacks 00DV "canonical localization inclusion"]
theorem localized_le_localized_of_smul_le
    (S : Submonoid R) {P Q : Submodule R M} (s : S) (h : s • P ≤ Q) :
    P.localized S ≤ Q.localized S := sorry

/-- If one localized scalar sends the top submodule into `P`, then `P` becomes top after
canonical localization. -/
@[stacks 00DV "canonical localized top criterion"]
theorem localized_eq_top_of_smul_top_le
    (S : Submonoid R) (P : Submodule R M) (s : S)
    (h : s • (⊤ : Submodule R M) ≤ P) : P.localized S = ⊤ := sorry

/-- The localization of the image of a submodule that becomes
all of the localized source is the range of the localized linear map. -/
@[stacks 05N6 "localized submodule image"]
theorem localized_map_eq_range
    (S : Submonoid R) (f : M →ₗ[R] N) (P : Submodule R M)
    (hP : P.localized S = ⊤) :
    (P.map f).localized S = LinearMap.range (LocalizedModule.map S f) := sorry

end Submodule
