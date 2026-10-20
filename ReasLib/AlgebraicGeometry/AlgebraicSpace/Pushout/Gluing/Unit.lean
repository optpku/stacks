/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing

/-- The unit of the pushout-gluing adjunction for a thickening and an affine morphism
of algebraic spaces is an isomorphism. -/
instance unitIsIso {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] :
    IsIso (adjunction i f).unit :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing
