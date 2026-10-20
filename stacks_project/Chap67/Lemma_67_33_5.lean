/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.DimensionFormula
import StacksCheckRecall

/-!
# Dimension formula for flat morphisms of algebraic spaces

A flat, locally finite-type morphism of locally Noetherian algebraic spaces
of relative dimension `d` adds `d` to local dimension at every source point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.33.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
locally Noetherian algebraic spaces over `S` which is flat, locally of finite
type and of relative dimension `d`. For every point `x` in `|X|` with image
`y` in `|Y|` we have `dimensionAt x = dimensionAt y + d`. -/
@[stacks 0AFH] #check
  (AlgebraicGeometry.AlgebraicSpace.dimensionAt_eq_image_add_relativeDimension_of_flat :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {d : ℕ} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    [LocallyOfFiniteType f] [RelativeDimension f d] (x : Points X),
    dimensionAt x = dimensionAt (Points.map f x) + (d : WithBot ℕ∞))

end AlgebraicGeometry.AlgebraicSpace
