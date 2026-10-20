/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Smooth morphisms of algebraic spaces are flat
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Smooth

/-- A smooth morphism of algebraic spaces is flat. -/
instance flat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Smooth f] : Flat f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Smooth
