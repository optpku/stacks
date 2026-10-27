/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.ProjectionFormula
import StacksCheckRecall

/-!
# Projection formula for smooth schemes

Integral Chow homology is interpreted componentwise on the clopen loci of constant
smooth dimension. This retains arbitrary smooth schemes and locally finite cycles;
the completed operations agree with ordinary total Chow operations where applicable.
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.BivariantClass.hasGysinMap_of_smooth :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y),
    BivariantClass.HasGysinMap f)

/- Lemma 42.62.4. A proper morphism between arbitrary schemes smooth over a field
has a Gysin map and satisfies the integral intersection projection formula. -/
@[stacks 0FFC] #check
  (AlgebraicGeometry.ChowGroup.hasGysinMap_and_intersectionProduct_projection_formula :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
      [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y) [IsProper f.left]
      (alpha : ChowGroup.DimensionCompleted X) (beta : ChowGroup.DimensionCompleted Y),
      BivariantClass.HasGysinMap f ∧
        ChowGroup.DimensionCompleted.map f
          (ChowGroup.DimensionCompleted.smoothIntersectionProduct X alpha
            (ChowGroup.DimensionCompleted.smoothGysinMap f beta)) =
          ChowGroup.DimensionCompleted.smoothIntersectionProduct Y
            (ChowGroup.DimensionCompleted.map f alpha) beta)
