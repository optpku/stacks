/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Noetherian

/-!
# Reaching a point in the closure of the image by a Noetherian valuative square

A finite-type morphism of algebraic stacks to a locally Noetherian target
admits a discrete valuation ring valuative square through any point in the
closure of its image.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 106.11.1: if `f : X ⟶ Y` is a finite-type morphism of algebraic
stacks over a scheme `S` and `Y` is locally Noetherian, then every point `y`
of `|Y|` in the closure of the image of `|f|` is the image of the closed
point of `Spec(A)` in a 2-commutative valuative square `Spec(K) ⟶ X` over
`Spec(A) ⟶ Y`, where `A` is a discrete valuation ring and `K` is its field
of fractions. -/
@[stacks 0H2B] #check
  (AlgebraicGeometry.AlgebraicStack.exists_dvrValuativeCommSq_of_mem_closure_range :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [FiniteType f] [IsLocallyNoetherian Y]
    {y : Points Y},
    y ∈ closure (Set.range (Points.map f)) →
      ∃ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R ∧ sq.closedPointImage = y)

end AlgebraicGeometry.AlgebraicStack
