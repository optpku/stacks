/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

/-!
# Equivalences of local rings

A ring equivalence between local rings is canonically a local homomorphism.  Registering this
fact once keeps constructions functorial in equivalences without consumer-side `letI` blocks.
-/

namespace RingEquiv

universe u v

/-- A ring equivalence between local rings is a local homomorphism. -/
instance instIsLocalHom {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) : IsLocalHom e.toRingHom :=
  letI : IsLocalHom e := isLocalHom_equiv e
  isLocalHom_toRingHom e

end RingEquiv
