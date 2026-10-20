/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.Descent
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.57.10: a fixed fibre-degree bound descends along a flat surjective left edge of a
commutative triangle, without changing the bound. -/
@[stacks 03JB] #check
  (AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy_of_comp_of_flat_of_surjective :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.Surjective f] {n : ℕ},
      AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy (f ≫ h) n →
        AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy h n)

/- Universal boundedness of fibre degrees descends along a flat surjective left edge. -/
#check
  (AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres_of_comp_of_flat_of_surjective :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.Surjective f],
      AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres (f ≫ h) →
        AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres h)
