/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Closed immersions of algebraic spaces are finite

A closed immersion of algebraic spaces over a scheme is finite and integral.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsFinite

/-- A closed immersion of algebraic spaces is finite. -/
instance of_isClosedImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsClosedImmersion f] : IsFinite f :=
  sorry

end IsFinite

namespace IsIntegralHom

/-- A closed immersion of algebraic spaces is integral. -/
instance of_isClosedImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsClosedImmersion f] :
    IsIntegralHom f :=
  sorry

end IsIntegralHom

end AlgebraicGeometry.AlgebraicSpace
