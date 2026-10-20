/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact

/-!
# Closed immersions of algebraic stacks are quasi-compact

A closed immersion of algebraic stacks is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A closed immersion of algebraic stacks is quasi-compact. -/
@[stacks 0CL1]
instance ClosedImmersion.quasiCompact {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f] :
    AlgebraicStack.QuasiCompact f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
