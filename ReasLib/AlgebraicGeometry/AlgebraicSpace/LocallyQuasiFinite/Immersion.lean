/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite

/-!
# Immersions are locally quasi-finite
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An immersion of algebraic spaces is locally quasi-finite. -/
instance locallyQuasiFinite_of_isImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsImmersion f] : LocallyQuasiFinite f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
