/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.ClosedImmersion
import StacksCheckRecall

/-!
# Dimension along closed immersions of algebraic stacks

A closed immersion of locally Noetherian algebraic stacks cannot increase
dimension at a point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.5.18: if `i : Z ⟶ X` is a closed immersion of locally Noetherian
algebraic stacks, and if `z ∈ |Z|` has image `x = Points.map i z` in `|X|`,
then `dimensionAt z ≤ dimensionAt x`. -/
@[stacks 0DRY] #check (AlgebraicGeometry.AlgebraicStack.dimensionAt_le_of_closedImmersion :
  ∀ {S : Scheme.{u}} {Z X : GroupoidsOver S}
    [AlgebraicStack Z] [AlgebraicStack X] [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    (i : Z ⟶ X) [ClosedImmersion i] (z : Points Z),
    dimensionAt z ≤ dimensionAt (Points.map i z))

end AlgebraicGeometry.AlgebraicStack
