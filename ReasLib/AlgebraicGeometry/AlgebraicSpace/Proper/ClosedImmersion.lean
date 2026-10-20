/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed immersions of algebraic spaces are proper

A closed immersion of algebraic spaces over a scheme is a proper morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Proper

/-- A closed immersion of algebraic spaces is a proper morphism. -/
@[stacks 04XZ]
instance of_isClosedImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsClosedImmersion f] : Proper f :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace
