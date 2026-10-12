/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
public import ReasLib.RingTheory.RingHom.Syntomic.Basic

@[expose] public section

/-!
# Syntomic and Local Complete Intersection Ring Homomorphisms

@stack 07D3

This leaf owns the intrinsic equivalence between syntomicity and flat local
complete-intersection ring homomorphisms.
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace Syntomic

/-- A ring homomorphism is syntomic exactly when it is flat and a local
complete intersection. -/
@[stacks 07D3 "syntomic ring maps"]
theorem iff_flat_and_isLocalCompleteIntersection (f : R →+* S) :
    f.Syntomic ↔ f.Flat ∧ f.IsLocalCompleteIntersection := sorry

/-- For a flat ring homomorphism, syntomicity is equivalent to being a local complete
intersection. -/
@[stacks 07D3 "flat specialization"]
theorem iff_isLocalCompleteIntersection_of_flat (f : R →+* S) (hflat : f.Flat) :
    f.Syntomic ↔ f.IsLocalCompleteIntersection := sorry

end Syntomic

end RingHom
