/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Smooth
public import ReasLib.RingTheory.Smooth.AtPrime

@[expose] public section

/-!
# Smoothness of ring homomorphisms at a prime

This leaf gives the map-level form of `Algebra.SmoothAtPrime`.  The canonical
owner is the underlying ring homomorphism; an `AlgHom` carries an additional
base algebra which is not part of this intrinsic map-level predicate.
@stack 00TB
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism is smooth at a target prime when it is smooth on a
principal-open neighbourhood of that prime. -/
@[stacks 00TB "smooth ring homomorphisms at a prime"]
def SmoothAtPrime (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  AtPrime (fun g ↦ g.Smooth) f q

/-- The map-level pointwise predicate agrees with the algebra-level predicate
for the algebra structure induced by an algebra map. -/
@[stacks 00TB "smoothness at a prime for an algebra map"]
theorem smoothAtPrime_algebraMap [Algebra R S] (q : PrimeSpectrum S) :
    SmoothAtPrime (algebraMap R S) q ↔ Algebra.SmoothAtPrime R S q := sorry

end RingHom
