/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Noetherian Targets of Finite-Type Maps

This leaf gives the map-level form of the standard fact that a finite-type
algebra over a Noetherian ring is Noetherian.  Finite presentation is a
strictly stronger input and should use this owner through
`RingHom.FiniteType.of_finitePresentation`.
-/

universe u v

namespace RingHom.FiniteType

/-- The target of a finite-type map from a Noetherian commutative ring is
Noetherian. -/
@[stacks 034Z "Noetherian target of a finite-type map"]
theorem isNoetherianRing
    {R : Type u} {A : Type v} [CommRing R] [IsNoetherianRing R] [CommRing A]
    {f : R →+* A} (hf : f.FiniteType) :
    IsNoetherianRing A := sorry

end RingHom.FiniteType
