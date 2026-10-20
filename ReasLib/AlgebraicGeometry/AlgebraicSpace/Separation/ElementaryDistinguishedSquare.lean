/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Separatedness from an elementary distinguished square

A morphism of algebraic spaces is separated if the two legs of an elementary
distinguished square are separated over the target and the comparison of fibre
products is closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Separated

/-- A morphism `g : X ⟶ Y` of algebraic spaces over a scheme is separated if
`(j : U ⟶ X, f : V ⟶ X)` is an elementary distinguished square, both `j ≫ g` and
`f ≫ g` are separated, and the canonical comparison `U ×_X V ⟶ U ×_Y V` is closed. -/
@[stacks 0F45]
theorem of_isElementaryDistinguishedSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (g : X ⟶ Y) {U V : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X)
    [IsElementaryDistinguishedSquare j f] [Separated (j ≫ g)] [Separated (f ≫ g)]
    [Closed (pullback.mapDesc j f g)] : Separated g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Separated
