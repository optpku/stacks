/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.RingHom.ULift
public import ReasLib.RingTheory.EssentialFiniteness.RingHom

@[expose] public section

/-!
# Essential finiteness and universe lifts

This leaf places the invariance of essentially finite type and essentially
finite presentation under the canonical two-sided ring-hom universe lift at
the essential-finiteness layer, rather than at the low-level lift constructor.

@stack 00QW
-/

universe u v w x

namespace RingHom.EssFiniteType

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The two-sided universe lift of an essentially finite-type ring homomorphism is
essentially of finite type. -/
@[stacks 00QW "essential finite type and universe lifts"]
theorem ulift {f : R →+* S} (hf : f.EssFiniteType) :
    (RingHom.ulift.{w, x} f).EssFiniteType := sorry

/-- Essential finite type is invariant under the canonical two-sided universe lift. -/
@[stacks 00QW "essential finite type invariant under universe lifts"]
theorem ulift_iff {f : R →+* S} :
    (RingHom.ulift.{w, x} f).EssFiniteType ↔ f.EssFiniteType := sorry

end RingHom.EssFiniteType

namespace RingHom.EssFinitePresentation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A bijective ring homomorphism is essentially of finite presentation. -/
@[stacks 00QW "bijective essentially finitely presented ring homomorphism"]
theorem of_bijective {f : R →+* S} (hf : Function.Bijective f) :
    f.EssFinitePresentation := sorry

/-- The two-sided universe lift of an essentially finitely presented ring homomorphism is
essentially of finite presentation. -/
@[stacks 00QW "essential finite presentation and universe lifts"]
theorem ulift {f : R →+* S} (hf : f.EssFinitePresentation) :
    (RingHom.ulift.{w, x} f).EssFinitePresentation := sorry

/-- Essential finite presentation is invariant under the canonical two-sided universe lift. -/
@[stacks 00QW "essential finite presentation invariant under universe lifts"]
theorem ulift_iff {f : R →+* S} :
    (RingHom.ulift.{w, x} f).EssFinitePresentation ↔ f.EssFinitePresentation := sorry

end RingHom.EssFinitePresentation
