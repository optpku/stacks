/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation.Factorization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 102.6.1: a finite type quasi-separated morphism `f : 𝒳 ⟶ Y` from an
algebraic stack to a quasi-compact quasi-separated algebraic space factors,
over `Y`, through a closed immersion `𝒳 ⟶ 𝒳'` into an algebraic stack of
finite presentation over `Y`. -/
@[stacks 0CQ1] #check
  (AlgebraicGeometry.AlgebraicStack.exists_closedImmersion_factorization_of_finiteType :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      {Y : AlgebraicSpace S} [AlgebraicSpace.IsQuasiCompact Y]
      [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
      (f : X ⟶ Y.toGroupoids) [FiniteType f] [QuasiSeparated f],
      ∃ (X' : GroupoidsOver S) (hX' : AlgebraicStack X')
        (f' : X' ⟶ Y.toGroupoids) (hf' : FinitePresentation f')
        (i : X ⟶ X') (hi : Groupoids.Hom.ClosedImmersion i),
        Nonempty (i ≫ f' ≅ f))
