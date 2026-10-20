/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension.Composition

/-!
# Relative dimensions of composites with a flat first morphism
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Relative dimensions of locally finite type morphisms add under composition
when the first morphism is flat. -/
instance instRelativeDimension_comp_of_flat {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : ℕ)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [Flat f] [RelativeDimension f r] [RelativeDimension g s] :
    RelativeDimension (f ≫ g) (r + s) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
