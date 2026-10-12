/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.OverField.Locality
public import ReasLib.RingTheory.RingHom.Fiber.Localization.CompleteIntersection
public import ReasLib.RingTheory.RingHom.Syntomic.Basic

@[expose] public section

/-!
# Principal-Open Locality of Syntomic Ring Homomorphisms

This leaf owns finite principal-open locality for the fiber condition and for
the intrinsic `RingHom.Syntomic` predicate.
-/

namespace RingHom

/-- Lemma 10.136.4: local-complete-intersection fibers are local on the
target for finite principal-open covers. -/
@[stacks 00SO "locality of local-complete-intersection fibers"]
theorem HasLocalCompleteIntersectionFibers.ofLocalizationSpanTarget :
    OfLocalizationSpanTarget HasLocalCompleteIntersectionFibers := sorry

namespace Syntomic

/-- Lemma 10.136.4: syntomicity is local on the target for finite
principal-open covers. -/
@[stacks 00SO "syntomic locality on the target"]
theorem ofLocalizationSpanTarget : OfLocalizationSpanTarget Syntomic := sorry

end Syntomic

end RingHom
