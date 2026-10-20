/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Inseparable
public import Mathlib.RingTheory.Ideal.GoingDown

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism satisfies going up if every specialization of the contraction
of a prime ideal lifts to a specialization of that prime ideal. -/
def HasGoingUp (φ : R →+* S) : Prop :=
  SpecializingMap (PrimeSpectrum.comap φ)

/-- A ring homomorphism satisfies going down if, for primes `p ≤ p'` in its domain
and a prime `P'` lying over `p'`, there is a prime `P ≤ P'` lying over `p`. -/
def HasGoingDown (φ : R →+* S) : Prop :=
  @Algebra.HasGoingDown R S _ _ φ.toAlgebra

end RingHom
