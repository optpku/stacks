/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Localized modules with invertible denominators

This leaf records the universal property of a localization in the special
case where every denominator already acts invertibly on the module.  A
unit criterion is kept as a proposition; concrete equivalences require an
explicit `IsLocalizedModule` instance, so unfinished proof debt cannot enter
their data.

@stack 00EK
@stack 051T
-/

@[expose] public section

universe u v

namespace IsLocalizedModule

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type v} [AddCommMonoid N] [Module R N]

/-- Tag `051T`: localization along any localized-module model preserves the
invertibility of a base-scalar action on an `R`-module. -/
@[stacks 051T "localized module preserves unit scalar action"]
theorem isUnit_algebraMap
    (S : Submonoid R) (f : M →ₗ[R] N) [IsLocalizedModule S f] {r : R}
    (h : IsUnit (algebraMap R (Module.End R M) r)) :
    IsUnit (algebraMap R (Module.End R N) r) := sorry

/-- Stacks 00EK: if every element of `S` acts invertibly on `M`, then the
identity map presents `M` as its own localization at `S`. -/
@[stacks 00EK "localized module identity by units"]
theorem idOfUnits (S : Submonoid R)
    (h : ∀ s : S, IsUnit (algebraMap R (Module.End R M) s)) :
    IsLocalizedModule S (LinearMap.id : M →ₗ[R] M) := sorry

end IsLocalizedModule

namespace LocalizedModule

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Tag `051T`: localizing a module preserves the invertibility of every
base-scalar action that was already invertible before localization. -/
@[stacks 051T "canonical localized module preserves unit scalar action"]
theorem isUnit_algebraMap
    (S : Submonoid R) {r : R}
    (h : IsUnit (algebraMap R (Module.End R M) r)) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule S M)) r) := sorry

/-- Tag `00EK`: when an explicitly supplied localization instance presents
`M` as its own localization at `S`, the canonical localized module is
`R`-linearly equivalent to `M`. -/
@[stacks 00EK "localized module identity localization equivalence"]
noncomputable def idLinearEquiv (S : Submonoid R)
    [IsLocalizedModule S (LinearMap.id : M →ₗ[R] M)] :
    LocalizedModule S M ≃ₗ[R] M :=
  IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S M)
    (LinearMap.id : M →ₗ[R] M)

/-- The identity-localization equivalence sends the canonical image of `m`
to `m`. -/
@[simp, stacks 00EK "localized module identity localization equivalence on generators"]
theorem idLinearEquiv_apply_mk (S : Submonoid R)
    [IsLocalizedModule S (LinearMap.id : M →ₗ[R] M)] (m : M) :
    idLinearEquiv S (LocalizedModule.mkLinearMap S M m) = m := sorry

/-- The inverse identity-localization equivalence sends `m` to its canonical
localized image. -/
@[simp, stacks 00EK "inverse localized module identity equivalence on generators"]
theorem idLinearEquiv_symm_apply (S : Submonoid R)
    [IsLocalizedModule S (LinearMap.id : M →ₗ[R] M)] (m : M) :
    (idLinearEquiv S).symm m = LocalizedModule.mkLinearMap S M m := sorry

/-- The identity-localization equivalence is a left inverse to the canonical
localization map. -/
@[stacks 00EK "localized module identity localization equivalence composition"]
theorem idLinearEquiv_comp_mkLinearMap (S : Submonoid R)
    [IsLocalizedModule S (LinearMap.id : M →ₗ[R] M)] :
    (idLinearEquiv S).toLinearMap.comp (LocalizedModule.mkLinearMap S M) =
      (LinearMap.id : M →ₗ[R] M) := sorry

namespace Away

/-- Tag `00EK`: an explicitly supplied identity localization instance away
from `r` gives the canonical equivalence from `M_r` to `M`. -/
@[stacks 00EK "away localized module identity equivalence"]
noncomputable def idLinearEquiv (r : R)
    [IsLocalizedModule (Submonoid.powers r) (LinearMap.id : M →ₗ[R] M)] :
    LocalizedModule.Away r M ≃ₗ[R] M :=
  LocalizedModule.idLinearEquiv (Submonoid.powers r)

/-- The away identity-localization equivalence sends the canonical image of
`m` to `m`. -/
@[simp, stacks 00EK "away localized module identity equivalence on generators"]
theorem idLinearEquiv_apply_mk (r : R)
    [IsLocalizedModule (Submonoid.powers r) (LinearMap.id : M →ₗ[R] M)] (m : M) :
    idLinearEquiv r
        (LocalizedModule.mkLinearMap (Submonoid.powers r) M m) = m := sorry

/-- The inverse away identity-localization equivalence sends `m` to its
canonical localized image. -/
@[simp, stacks 00EK "inverse away localized module identity equivalence on generators"]
theorem idLinearEquiv_symm_apply (r : R)
    [IsLocalizedModule (Submonoid.powers r) (LinearMap.id : M →ₗ[R] M)] (m : M) :
    (idLinearEquiv r).symm m =
      LocalizedModule.mkLinearMap (Submonoid.powers r) M m := sorry

end Away

end LocalizedModule
