/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CompleteIntersection.Fiber
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Syntomic ring homomorphisms

This module owns the elementary ring-map predicate for syntomic morphisms and
its projections.  Stability results belong in separate leaves.
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

open PrimeSpectrum

/-- A ring homomorphism has local complete-intersection fibers when every
residue-field fiber is a local complete intersection. -/
@[stacks 00SL "local complete-intersection fibers"]
def HasLocalCompleteIntersectionFibers (f : R →+* S) : Prop :=
  ∀ p : PrimeSpectrum R,
    Fiber.IsLocalCompleteIntersection f p.asIdeal

/-- A ring map has local complete-intersection fibers exactly when its fiber at every prime has
the pointwise local complete-intersection property. -/
@[stacks 00SL "pointwise specification of local complete-intersection fibers"]
theorem hasLocalCompleteIntersectionFibers_iff (f : R →+* S) :
    f.HasLocalCompleteIntersectionFibers ↔
      ∀ p : PrimeSpectrum R, Fiber.IsLocalCompleteIntersection f p.asIdeal := sorry

/-- A ring homomorphism is syntomic when it is flat, of finite presentation,
and has local complete-intersection fibers. -/
@[stacks 00SL]
def Syntomic (f : R →+* S) : Prop :=
  f.Flat ∧ f.FinitePresentation ∧ f.HasLocalCompleteIntersectionFibers

namespace Syntomic

/-- A syntomic ring homomorphism is flat. -/
@[stacks 00SL "flatness of syntomic ring maps"]
theorem flat {f : R →+* S} (hf : f.Syntomic) : f.Flat := sorry

/-- A syntomic ring homomorphism is finitely presented. -/
@[stacks 00SL "finite presentation of syntomic ring maps"]
theorem finitePresentation {f : R →+* S} (hf : f.Syntomic) : f.FinitePresentation := sorry

/-- A syntomic ring homomorphism has local complete-intersection fibers. -/
@[stacks 00SL "local complete-intersection fibers of syntomic maps"]
theorem hasLocalCompleteIntersectionFibers {f : R →+* S} (hf : f.Syntomic) :
    f.HasLocalCompleteIntersectionFibers := sorry

end Syntomic

end RingHom
