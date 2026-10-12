/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Unramified ring homomorphisms

This leaf gives the intrinsic ring-hom view of the canonical algebra-level
unramified predicate.  It lets consumers state properties of a particular map
without installing its induced algebra structure in the surrounding context.

@stack 00UU
-/

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A commutative ring homomorphism is unramified when the algebra structure
it induces on its codomain is unramified. -/
@[algebraize RingHom.Unramified.toAlgebra,
  stacks 00UU "unramified ring homomorphism"]
def Unramified (f : R →+* S) : Prop :=
  @Algebra.Unramified R _ S _ f.toAlgebra

namespace Unramified

/-- The intrinsic ring-hom predicate recovers the canonical algebra-level
unramified structure induced by the map. -/
@[stacks 00UU "unramified ring homomorphism"]
theorem toAlgebra {f : R →+* S} (hf : f.Unramified) :
    @Algebra.Unramified R _ S _ f.toAlgebra := sorry

end Unramified

/-- The intrinsic ring-hom predicate on an algebra map is equivalent to the
ambient algebra-level unramified predicate. -/
@[stacks 00UU "unramified algebra maps"]
theorem unramified_algebraMap [Algebra R S] :
    (algebraMap R S).Unramified ↔ Algebra.Unramified R S := sorry

end RingHom
