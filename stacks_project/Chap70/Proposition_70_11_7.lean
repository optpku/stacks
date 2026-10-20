/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.Factorization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Proposition 70.11.7: a finite type separated morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S`, with `Y` quasi-compact and quasi-separated,
factors as a closed immersion `X ⟶ X'` over `Y` followed by a separated morphism
`X' ⟶ Y` of finite presentation. -/
@[stacks 0873] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_closedImmersion_factorization_of_finiteType_separated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.FiniteType f] [AlgebraicSpace.Separated f]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y],
      (MorphismProperty.comp
        (@AlgebraicSpace.IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
        ((@AlgebraicSpace.FinitePresentation S : MorphismProperty (AlgebraicSpace S)) ⊓
          (@AlgebraicSpace.Separated S : MorphismProperty (AlgebraicSpace S)))) f)
