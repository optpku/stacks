/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.ActionAlgebraic
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open GroupoidAlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Action

/- Lemma 97.18.2: let `S` be a scheme and let `B` be an algebraic space over
`S`. Let `G` be a group algebraic space over `B`. Let `X` be an algebraic space
over `B` and let `a : G ×_B X ⟶ X` be an action of `G` on `X` over `B`. The
quotient stack `[X / G]` is an algebraic stack if and only if there exists a
morphism of algebraic spaces `φ : X' ⟶ X` such that `G ×_B X' ⟶ X`,
`(g, x') ↦ a(g, φ(x'))` is a surjection of sheaves, and the two projections
`X'' ⟶ X'` of the algebraic space `X''` given by
`T ↦ {(x'₁, g, x'₂) | φ(x'₁) = a(g, φ(x'₂))}` are flat and locally of finite
presentation. Formalized for `G : GroupAlgebraicSpace B` and `X : Action G`,
with `[X / G]` as `SmallQuotient.quotientStack (ofAction G X)`, the action as
`actionTarget G X`, the orbit map as `orbitMap G X φ`, sheaf surjection as
`Presheaf.IsLocallySurjective` on `Scheme.fppfTopology.over S`, `X''` as
`((ofAction G X).pullback φ).R`, and the two projections flat and locally of
finite presentation as `Flat ((ofAction G X).pullback φ)` and
`LocallyOfFinitePresentation ((ofAction G X).pullback φ)`. -/

@[stacks 06PK] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.Action.isAlgebraicStack_quotientStack_iff :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (X : Action G),
      AlgebraicStack (SmallQuotient.quotientStack (ofAction G X)) ↔
        ∃ (X' : Over B) (φ : X' ⟶ X.X),
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
              (orbitMap G X φ).left ∧
            GroupoidAlgebraicSpace.Flat ((ofAction G X).pullback φ) ∧
              GroupoidAlgebraicSpace.LocallyOfFinitePresentation ((ofAction G X).pullback φ))

end AlgebraicGeometry.GroupAlgebraicSpace.Action
