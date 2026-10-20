/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.LocalizedModule.Equiv
public import ReasLib.RingTheory.Localization.Ideal

/-!
# Prime-localized module equivalences

This leaf exposes the canonical prime-local views of two localization comparisons:
localizing a linear equivalence, and localizing an ideal.  The underlying arbitrary-submonoid
owners remain in `LocalizedModule.mapEquiv` and `Ideal.localizationMapEquiv`; these declarations
only choose `p.primeCompl` and restrict scalars to the original ring for the common downstream
interface.
-/

@[expose] public section

universe u v w

namespace LocalizedModule.AtPrime

variable {R : Type u} [CommSemiring R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- A linear equivalence localizes at a prime and remains an `R`-linear equivalence. -/
@[stacks 0523 "prime-localized linear equivalence"]
noncomputable def mapEquiv (p : Ideal R) [p.IsPrime] (e : M ≃ₗ[R] N) :
    LocalizedModule.AtPrime p M ≃ₗ[R] LocalizedModule.AtPrime p N :=
  (LocalizedModule.mapEquiv p.primeCompl e).restrictScalars R

/-- The prime-localized equivalence sends a canonical numerator to the localized image of that
numerator. -/
@[simp, stacks 0523 "prime-localized linear equivalence on generators"]
theorem mapEquiv_apply_mk (p : Ideal R) [p.IsPrime] (e : M ≃ₗ[R] N) (m : M) :
    mapEquiv p e (LocalizedModule.mkLinearMap p.primeCompl M m) =
      LocalizedModule.mkLinearMap p.primeCompl N (e m) := sorry

end LocalizedModule.AtPrime

namespace Ideal.AtPrime

variable {R : Type u} [CommSemiring R]

/-- The localization of an ideal at a prime is canonically its ideal map to the prime-localized
ring, viewed as an `R`-linear equivalence. -/
@[stacks 0523 "prime-localized ideal comparison"]
noncomputable abbrev mapEquiv (p : Ideal R) [p.IsPrime] (I : Ideal R) :
    LocalizedModule.AtPrime p I ≃ₗ[R]
      Ideal.map (algebraMap R (Localization.AtPrime p)) I :=
  Ideal.localizationMapEquiv p.primeCompl I

/-- The prime-localized ideal comparison sends a canonical numerator to its mapped ideal
generator. -/
@[simp, stacks 0523 "prime-localized ideal comparison on generators"]
theorem mapEquiv_apply_mk (p : Ideal R) [p.IsPrime] (I : Ideal R) (x : I) :
    mapEquiv p I (LocalizedModule.mkLinearMap p.primeCompl I x) =
      Algebra.idealMap I (S := Localization.AtPrime p) x := sorry

end Ideal.AtPrime
