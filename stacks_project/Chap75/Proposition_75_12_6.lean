/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Comparison.Noetherian

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Proposition 75.12.6. Let `S` be a scheme. Let `X` be a Noetherian algebraic space
over `S`. Then the functor 75.5.1.1,
`comparison X : DerivedCategory (QCoh X) ⥤ DerivedQCoh X`, is an equivalence with
quasi-inverse given by `RQ_X`, identified with
`inclusion X ⋙ QCoh.Derived.coherator X`. -/
@[stacks 09TN] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.comparison_isQuasiInverse_of_isNoetherian :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X],
      (DerivedQCoh.comparison X).IsQuasiInverse
        (DerivedQCoh.inclusion X ⋙ QCoh.Derived.coherator X))

/- The equivalence clause of Proposition 75.12.6. -/
@[stacks 09TN] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.comparisonIsEquivalence :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsNoetherian X],
      (DerivedQCoh.comparison X).IsEquivalence)
