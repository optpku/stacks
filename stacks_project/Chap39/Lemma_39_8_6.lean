/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.AffineOpen
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.GroupScheme

/- Lemma 39.8.6: Over an algebraically closed field, every finite family of rational
points of a locally algebraic group scheme is contained in an affine open. -/
@[stacks 0B7S]
#check (AlgebraicGeometry.GroupScheme.exists_affineOpen_containing_rationalPoints :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (G : SchemeOverField k) [GrpObj G] [LocallyAlgebraic G] {n : ℕ}
    (g : Fin n → (𝟙_ (SchemeOverField k) ⟶ G)),
    ∃ U : G.left.affineOpens,
      Set.range (fun i ↦ (g i).left (IsLocalRing.closedPoint k)) ⊆
        ((U : G.left.Opens) : Set G.left))

end AlgebraicGeometry.GroupScheme
