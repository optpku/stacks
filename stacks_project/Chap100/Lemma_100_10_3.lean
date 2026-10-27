/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.ClosedImmersion.Factorization
import StacksCheckRecall

/-!
# Maps from reduced algebraic stacks into closed substacks

A 1-morphism from a reduced algebraic stack factors through a closed substack if
and only if the induced map on points lands in that closed substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Groupoids.Hom
open scoped Bicategory

universe u

/- Lemma 100.10.3: A morphism from a reduced algebraic stack factors through
a closed substack if and only if its image on points lies in that substack. -/
@[stacks 050B] #check
  (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion.factorsThrough_iff_range_subset :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      [AlgebraicStack.IsReduced Y] (i : Z ⟶ X) [ClosedImmersion i] (f : Y ⟶ X),
      FactorsThrough f i ↔
        Set.range (AlgebraicStack.Points.map f) ⊆ Set.range (AlgebraicStack.Points.map i))

#check
  (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion.lift_unique :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (i : Z ⟶ X) [ClosedImmersion i] {f : Y ⟶ X} {g g' : Y ⟶ Z},
      (g ≫ i ≅ f) → (g' ≫ i ≅ f) → Nonempty (g ≅ g'))
