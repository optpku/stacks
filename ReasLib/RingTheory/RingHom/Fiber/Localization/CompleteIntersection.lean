/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.OverField.Locality
public import ReasLib.RingTheory.RingHom.Fiber.Localization

@[expose] public section

/-!
# Complete-Intersection Fibers and Principal Localization

This leaf transports the local complete-intersection condition across the
canonical residue-field-fiber/principal-localization equivalence.
-/

universe u v

namespace Ideal.Fiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.136.4: taking a residue-field fiber and localizing the target at
`g` preserves the local complete-intersection condition exactly. -/
@[stacks 00SO "local complete intersections on localized fibers"]
theorem isLocalCompleteIntersection_localizationAway_iff
    (p : Ideal R) [p.IsPrime] (g : S) :
    IsLocalCompleteIntersection p.ResidueField (p.Fiber (Localization.Away g)) ↔
      IsLocalCompleteIntersection p.ResidueField
        (Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) g)) := sorry

end Ideal.Fiber
