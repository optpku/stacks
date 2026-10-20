/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative scalar actions at prime localizations

Canonical relative local-ring maps and the algebra structure
`Localization.AtPrime.algebraOfLiesOver` induce explicit module actions. Keeping these actions
explicit avoids localization-instance diamonds.
-/

@[expose] public section

universe u v w x

namespace Localization.AtPrime.Relative

variable {R : Type u} [CommSemiring R]
variable {S : Type v} [CommSemiring S] [Algebra R S]
variable {M : Type w} [AddCommMonoid M] [Module S M]

/-- The action of `Localization.AtPrime p` on `LocalizedModule.AtPrime P M` induced by the
canonical local-ring map when `P` lies over `p`. -/
@[stacks 00HT "relative prime-localization module action"]
noncomputable abbrev moduleOfLiesOver
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    Module (Localization.AtPrime p) (LocalizedModule.AtPrime P M) :=
  Module.compHom (LocalizedModule.AtPrime P M)
    (Localization.localRingHom p P (algebraMap R S) Ideal.LiesOver.over)

/-- The action of `Localization.AtPrime (P.under R)` on `LocalizedModule.AtPrime P M` induced by
the ambient algebra map `R → S`. -/
@[stacks 00HT "relative prime-localization module action"]
noncomputable abbrev algebraMapModule (P : Ideal S) [P.IsPrime] :
    Module (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime P M) :=
  moduleOfLiesOver (P.under R) P

/-- The relative action of `Localization.AtPrime (P.under R)` extends the original `R`-action
on the localized module. -/
@[stacks 00HT "relative prime-localization base scalar tower"]
theorem algebraMapModule_isScalarTower [Module R M] [IsScalarTower R S M]
    (P : Ideal S) [P.IsPrime] :
    -- Local instance justification (instance diamond): select the named relative action.
    letI : Module (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime P M) :=
      algebraMapModule (R := R) P
    IsScalarTower R (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime P M) := sorry

/-- The relative module action on `LocalizedModule.AtPrime P M` is compatible with Mathlib's
canonical algebra `Localization.AtPrime p →ₐ[R] Localization.AtPrime P`. -/
@[stacks 00HT "relative prime-localization scalar tower"]
theorem moduleOfLiesOver_isScalarTower
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    -- Local instance justification (instance diamond): select the canonical relative algebra.
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
      Localization.AtPrime.algebraOfLiesOver p P
    -- Local instance justification (instance diamond): select the named relative action.
    letI : Module (Localization.AtPrime p) (LocalizedModule.AtPrime P M) :=
      moduleOfLiesOver p P
    IsScalarTower (Localization.AtPrime p) (Localization.AtPrime P)
      (LocalizedModule.AtPrime P M) := sorry

end Localization.AtPrime.Relative

namespace LocalizedModule

variable {R : Type u} [CommSemiring R]
variable {S : Type v} [CommSemiring S] [Algebra R S]
variable {M : Type w} [AddCommMonoid M] [Module S M]
variable {N : Type x} [AddCommMonoid N] [Module S N]

/-- The localization of an `S`-linear map at `q`, regarded as a linear map over the local base
ring `Localization.AtPrime (q.under R)`.  The relative algebra and module actions are confined to
this construction. -/
@[stacks 00HT "relative prime-localized module map"]
noncomputable def mapAtPrimeOver (q : Ideal S) [q.IsPrime] (f : M →ₗ[S] N) :
    -- Local instance justification (instance diamond): select the canonical relative algebra.
    letI : Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver (q.under R) q
    -- Local instance justification (instance diamond): select the named action on the source.
    letI : Module (Localization.AtPrime (q.under R)) (LocalizedModule.AtPrime q M) :=
      Localization.AtPrime.Relative.algebraMapModule (R := R) (M := M) q
    -- Local instance justification (instance diamond): select the named action on the target.
    letI : Module (Localization.AtPrime (q.under R)) (LocalizedModule.AtPrime q N) :=
      Localization.AtPrime.Relative.algebraMapModule (R := R) (M := N) q
    -- Local instance justification (instance diamond): pin the source scalar tower.
    letI : IsScalarTower (Localization.AtPrime (q.under R))
        (Localization.AtPrime q) (LocalizedModule.AtPrime q M) :=
      SMul.comp.isScalarTower
        (Localization.localRingHom (q.under R) q (algebraMap R S) rfl)
    -- Local instance justification (instance diamond): pin the target scalar tower.
    letI : IsScalarTower (Localization.AtPrime (q.under R))
        (Localization.AtPrime q) (LocalizedModule.AtPrime q N) :=
      SMul.comp.isScalarTower
        (Localization.localRingHom (q.under R) q (algebraMap R S) rfl)
    LocalizedModule.AtPrime q M →ₗ[Localization.AtPrime (q.under R)] LocalizedModule.AtPrime q N :=
  -- Local instance justification (instance diamond): select the canonical relative algebra.
  letI : Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver (q.under R) q
  -- Local instance justification (instance diamond): select the named action on the source.
  letI : Module (Localization.AtPrime (q.under R)) (LocalizedModule.AtPrime q M) :=
    Localization.AtPrime.Relative.algebraMapModule (R := R) (M := M) q
  -- Local instance justification (instance diamond): select the named action on the target.
  letI : Module (Localization.AtPrime (q.under R)) (LocalizedModule.AtPrime q N) :=
    Localization.AtPrime.Relative.algebraMapModule (R := R) (M := N) q
  -- Local instance justification (instance diamond): pin the source scalar tower.
  letI : IsScalarTower (Localization.AtPrime (q.under R))
      (Localization.AtPrime q) (LocalizedModule.AtPrime q M) :=
    SMul.comp.isScalarTower
      (Localization.localRingHom (q.under R) q (algebraMap R S) rfl)
  -- Local instance justification (instance diamond): pin the target scalar tower.
  letI : IsScalarTower (Localization.AtPrime (q.under R))
      (Localization.AtPrime q) (LocalizedModule.AtPrime q N) :=
    SMul.comp.isScalarTower
      (Localization.localRingHom (q.under R) q (algebraMap R S) rfl)
  (LocalizedModule.map q.primeCompl f).restrictScalars (Localization.AtPrime (q.under R))

/-- The relative prime-localized map has the same underlying function as Mathlib's canonical
localized linear map. -/
@[simp, stacks 00HT "relative prime-localized module map on elements"]
theorem mapAtPrimeOver_apply (q : Ideal S) [q.IsPrime] (f : M →ₗ[S] N)
    (m : LocalizedModule.AtPrime q M) :
    mapAtPrimeOver (R := R) q f m = LocalizedModule.map q.primeCompl f m := sorry

end LocalizedModule
