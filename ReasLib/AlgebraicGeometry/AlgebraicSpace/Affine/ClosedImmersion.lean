/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion

/-!
# Affineness of closed immersions of algebraic spaces

Closed immersions of algebraic spaces are affine morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace AlgebraicSpace

namespace IsClosedImmersion

/-- A closed immersion of algebraic spaces is an affine morphism. -/
instance affine {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsClosedImmersion f] : Affine f :=
  sorry

/-- The closed-immersion morphism property is contained in the affine morphism property. -/
theorem le_affine {S : Scheme.{u}} :
    (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S)) ≤
      (@Affine S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end IsClosedImmersion

end AlgebraicSpace

end AlgebraicGeometry
