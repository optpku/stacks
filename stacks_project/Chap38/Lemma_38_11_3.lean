/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.DenseOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 38.11.3: a flat morphism locally of finite type has relative dimension at most
`e` if it has that bound over a dense open and either the morphism is locally of finite
presentation or the open is retrocompact. -/
@[stacks 081L] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE.of_restrict_of_flat :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      [AlgebraicGeometry.Flat f] →
      [AlgebraicGeometry.LocallyOfFiniteType f] →
      (U : S.Opens) →
      (e : ℕ) →
      Dense (U : Set S) →
      [AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE (f ∣_ U) e] →
      (AlgebraicGeometry.LocallyOfFinitePresentation f ∨
        IsRetrocompact (U : Set S)) →
      AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE f e)
