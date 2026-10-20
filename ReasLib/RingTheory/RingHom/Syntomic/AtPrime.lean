/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.RingHom
public import ReasLib.RingTheory.RingHom.Fiber.Local.CompleteIntersection
public import ReasLib.RingTheory.RingHom.Local.AtPrime
public import ReasLib.RingTheory.RingHom.Syntomic.Basic

@[expose] public section

/-!
# Syntomic Ring Homomorphisms at a Prime

The elementary pointwise predicates in this leaf are phrased for an arbitrary
ring homomorphism, so users do not need to install an ambient `Algebra`
instance merely to formulate a local criterion.

@stack 00SY
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism is syntomic at `q` when it is syntomic on a
principal-open neighbourhood of `q`. -/
@[stacks 00SY "syntomic at a prime"]
def SyntomicAtPrime (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  AtPrime (fun g ↦ g.Syntomic) f q

namespace SyntomicAtPrime

/-- Syntomicity at a target prime is the existence of a syntomic restriction
to a principal-open neighborhood. -/
theorem iff_exists_away (f : R →+* S) (q : PrimeSpectrum S) :
    f.SyntomicAtPrime q ↔
      ∃ g : S, g ∉ q.asIdeal ∧
        ((algebraMap S (Localization.Away g)).comp f).Syntomic := sorry

/-- The local finite-presentation, flatness, and complete-intersection-fiber
criterion for syntomicity at a target prime. -/
@[stacks 00SY "local criterion for syntomicity at a prime"]
def LocalCriterion (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  f.FinitePresentationAt q ∧ f.FlatAt q ∧
    RingHom.Fiber.IsCompleteIntersectionAt f q

end SyntomicAtPrime

namespace Syntomic

/-- A syntomic ring homomorphism is syntomic at every target prime. -/
theorem atPrime {f : R →+* S} (hf : f.Syntomic) (q : PrimeSpectrum S) :
    f.SyntomicAtPrime q := sorry

end Syntomic

namespace HasLocalCompleteIntersectionFibers

/-- Local complete-intersection fibers give the complete-intersection property
of the canonical local fiber at every target prime. -/
@[stacks 00SY "complete-intersection fiber at a prime"]
theorem isCompleteIntersectionAt {f : R →+* S}
    (hf : f.HasLocalCompleteIntersectionFibers) (q : PrimeSpectrum S) :
    RingHom.Fiber.IsCompleteIntersectionAt f q := sorry

end HasLocalCompleteIntersectionFibers

namespace SyntomicAtPrime

/-- The relative-global-complete-intersection neighbourhood criterion is
equivalent to syntomicity at a target prime. -/
@[stacks 00SY "syntomic and relative global complete intersection at a prime"]
theorem iff_relativeGlobalCompleteIntersection {f : R →+* S} (q : PrimeSpectrum S) :
    f.SyntomicAtPrime q ↔ IsRelativeGlobalCompleteIntersection.AtPrime f q := sorry

/-- The finite-presentation, local-flatness, and local-fiber-complete-
intersection criterion is equivalent to syntomicity at a target prime. -/
@[stacks 00SY "local criterion for syntomicity at a prime"]
theorem iff_localCriterion {f : R →+* S} (q : PrimeSpectrum S) :
    f.SyntomicAtPrime q ↔ SyntomicAtPrime.LocalCriterion f q := sorry

/-- Syntomicity at a target prime supplies finite presentation on a principal-
open neighbourhood. -/
theorem finitePresentationAt {f : R →+* S} {q : PrimeSpectrum S}
    (hf : f.SyntomicAtPrime q) : f.FinitePresentationAt q := sorry

/-- Syntomicity at a target prime supplies flatness of the induced local ring
homomorphism. -/
theorem flatAt {f : R →+* S} {q : PrimeSpectrum S}
    (hf : f.SyntomicAtPrime q) : f.FlatAt q := sorry

/-- Syntomicity at a target prime supplies a complete-intersection canonical
local fiber. -/
@[stacks 00SY "syntomicity gives a complete-intersection fiber at a prime"]
theorem isCompleteIntersectionAt {f : R →+* S} {q : PrimeSpectrum S}
    (hf : f.SyntomicAtPrime q) : RingHom.Fiber.IsCompleteIntersectionAt f q := sorry

end SyntomicAtPrime

namespace IsRelativeGlobalCompleteIntersection.AtPrime

/-- A relative-global-complete-intersection neighbourhood is syntomic at the
same target prime. -/
theorem syntomicAt {f : R →+* S} {q : PrimeSpectrum S}
    (hf : IsRelativeGlobalCompleteIntersection.AtPrime f q) : f.SyntomicAtPrime q := sorry

end IsRelativeGlobalCompleteIntersection.AtPrime

namespace SyntomicAtPrime.LocalCriterion

/-- The local finite-presentation, flatness, and complete-intersection-fiber
criterion produces a relative-global-complete-intersection neighbourhood. -/
theorem relativeCIAt {f : R →+* S} {q : PrimeSpectrum S}
    (hf : SyntomicAtPrime.LocalCriterion f q) :
    IsRelativeGlobalCompleteIntersection.AtPrime f q := sorry

end SyntomicAtPrime.LocalCriterion

/-- At a target prime, syntomicity, the existence of a relative global complete
intersection neighbourhood, and the local finite-presentation, flatness, and
complete-intersection-fiber criterion are equivalent. -/
@[stacks 00SY "syntomicity at a prime"]
theorem SyntomicAtPrime.tfae (f : R →+* S) (q : PrimeSpectrum S) :
    List.TFAE
      [ f.SyntomicAtPrime q
      , IsRelativeGlobalCompleteIntersection.AtPrime f q
      , SyntomicAtPrime.LocalCriterion f q
      ] := sorry

end RingHom
