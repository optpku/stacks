/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigFlat

/-!
# Composition of rig-flat morphisms

The composition of rig-flat morphisms of locally Noetherian formal algebraic
spaces is again rig-flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigFlat

/-- The composition of rig-flat morphisms of locally Noetherian formal algebraic
spaces over a scheme is rig-flat. -/
instance comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [RigFlat f] [RigFlat g] : RigFlat (f ≫ g) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigFlat
