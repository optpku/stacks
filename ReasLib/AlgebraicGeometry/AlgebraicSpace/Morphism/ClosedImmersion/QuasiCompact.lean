/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Quasi-compactness of closed immersions

Closed immersions of algebraic spaces over a scheme are quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/-- A closed immersion of algebraic spaces is quasi-compact. -/
@[instance]
theorem AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.quasiCompact {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsClosedImmersion f] : QuasiCompact f :=
  sorry

/-- Closed immersions of algebraic spaces are quasi-compact as a morphism property. -/
theorem AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.le_quasiCompact {S : Scheme.{u}} :
    (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S)) ≤
      (@QuasiCompact S : MorphismProperty (AlgebraicSpace S)) :=
  sorry
