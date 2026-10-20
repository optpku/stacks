/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Comparison
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace

/- Lemma 78.20.3: there is a canonical `2`-morphism `α : π ∘ s ⟶ π ∘ t` making the square
`𝒮_R ⇉ 𝒮_U ⟶ [U/R]` `2`-commutative. -/
@[stacks 044S] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.sourceTarget :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      AlgebraicGeometry.GroupoidAlgebraicSpace.atlasSource G ⟶
        AlgebraicGeometry.GroupoidAlgebraicSpace.atlasTarget G)
