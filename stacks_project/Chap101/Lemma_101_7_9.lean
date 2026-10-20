/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.QuasiCompact

/-!
# Reaching a point in the closure of the image by a quasi-compact valuative square

A quasi-compact morphism of algebraic stacks admits a valuative square through
any point in the closure of its image.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.7.9: if `f : X ⟶ Y` is a quasi-compact morphism of algebraic
stacks over a scheme `S`, then every point `y` of `|Y|` in the closure of the
image of `|f|` is the image of the closed point of `Spec(A)` in a 2-commutative
valuative square `Spec(K) ⟶ X` over `Spec(A) ⟶ Y`, where `A` is a valuation
ring and `K` is its field of fractions. -/
@[stacks 0CL2] #check
  (AlgebraicGeometry.AlgebraicStack.exists_valuativeCommSq_of_mem_closure_range :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicStack.QuasiCompact f]
    {y : AlgebraicGeometry.AlgebraicStack.Points Y},
    y ∈ closure (Set.range (AlgebraicGeometry.AlgebraicStack.Points.map f)) →
      ∃ sq : AlgebraicGeometry.AlgebraicStack.ValuativeCommSq f, sq.closedPointImage = y)

end AlgebraicGeometry.AlgebraicStack
