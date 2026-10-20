/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.Composition

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.57.4: fixed fibre-degree bounds multiply under composition. -/
@[stacks 03J6] #check (AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy_comp :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {n m : ℕ},
    AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy f n →
      AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy g m →
        AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy (f ≫ g) (n * m))

#check (AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres_comp :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres f →
      AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres g →
        AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres (f ≫ g))
