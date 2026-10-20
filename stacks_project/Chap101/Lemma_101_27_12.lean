/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.Fppf
import StacksCheckRecall

/-!
# Permanence of local finite presentation for morphisms of algebraic stacks

If `X ⟶ Z` is locally of finite presentation and `X ⟶ Y` is surjective, flat,
and locally of finite presentation, then `Y ⟶ Z` is locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/- Lemma 101.27.12: Let `X ⟶ Y ⟶ Z` be morphisms of algebraic stacks. If
`X ⟶ Z` is locally of finite presentation and `X ⟶ Y` is surjective, flat,
and locally of finite presentation, then `Y ⟶ Z` is locally of finite
presentation. -/
@[stacks 06Q9] #check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.of_comp_of_fppf :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ g)]
      [Surjective f] [Flat f] [LocallyOfFinitePresentation f],
      LocallyOfFinitePresentation g)

end AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
