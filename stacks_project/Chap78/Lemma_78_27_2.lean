/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Gerbe
import StacksCheckRecall

/-!
# The classifying morphism of a group algebraic space is a gerbe

This file records that the canonical morphism `[B/G] ⟶ 𝒮_B` of Lemma 78.20.2
exhibits the quotient stack of the trivial `G`-action on `B` as a gerbe over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidAlgebraicSpace AlgebraicGeometry.GroupAlgebraicSpace

noncomputable section

universe u

/- Lemma 78.27.2. Let `S` be a scheme. Let `B` be an algebraic space over `S`. Let
`G` be a group algebraic space over `B`. Endow `B` with the trivial action of `G`.
The morphism `[B/G] ⟶ 𝒮_B` of Lemma 78.20.2 turns `[B/G]` into a gerbe over `B`.
Here `[B/G]` is `(ofAction G (trivialAction G)).quotientStack`, `𝒮_B` is
`stackInSets B`, and the morphism is `toBase (ofAction G (trivialAction G))`. -/
@[stacks 06PF]
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.toBase_trivialAction_isGerbeMorphism :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupAlgebraicSpace B),
    CategoryTheory.CartesianBasedFunctor.IsGerbeMorphism
      (AlgebraicGeometry.Scheme.fppfTopology.over S)
      (AlgebraicGeometry.GroupoidAlgebraicSpace.toBase
        (AlgebraicGeometry.GroupoidAlgebraicSpace.ofAction G
          (AlgebraicGeometry.GroupAlgebraicSpace.trivialAction G))))
