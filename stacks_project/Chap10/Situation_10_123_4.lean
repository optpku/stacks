module

public import ReasLib.RingTheory.Conductor.Polynomial
import StacksCheckRecall

@[expose] public section

/-!
# Situation 10.123.4
@stack 00PW

The source setup consists of a finite polynomial map, its conductor, and the
integrally closed constant-image hypothesis.
-/

universe u v

section

open Polynomial

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom

/-
Situation 10.123.4 introduces the conductor ideal
`J = conductor R (φ X)` for the `R`-algebra structure on `S` induced by `φ.comp C`.
-/
@[stacks 00PW "finite polynomial map and conductor"]
#check ∀ φ : Polynomial R →+* S, φ.Finite →
  letI : Algebra R S := (φ.comp C).toAlgebra
  conductor R (φ X)

/-
Situation 10.123.4 assumes that the constant-image subring `((φ.comp C).range)` is integrally
closed in `S`. The source-facing owner for that hypothesis is the specialized proposition
`IsIntegrallyClosedIn ((φ.comp C).range) S`.
-/
@[stacks 00PW "integrally closed constant image"]
#check ∀ φ : Polynomial R →+* S, φ.Finite → IsIntegrallyClosedIn (φ.comp C).range S

/-
For the source-facing reformulation of integrally closed image, use the canonical owner theorem
`Subring.isIntegrallyClosedIn_iff` directly at `((φ.comp C).range)`.
-/
@[stacks 00PW "integrally closed image criterion"]
#check @Subring.isIntegrallyClosedIn_iff

@[stacks 00PW "polynomial-map conductor membership"]
#check @RingHom.PolynomialConductor.mem_iff

end RingHom

end
