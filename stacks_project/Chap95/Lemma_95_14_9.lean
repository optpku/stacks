/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.Category
import StacksCheckRecall

/-!
# Lemma 95.14.9

The functor `p : G-Torsors ⟶ (Sch/S)_fppf` is a stack in groupoids, up to the
small-fiber replacement of Remark 8.4.9.
Fiberwise essential smallness supplies the size condition for that replacement.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

/- Lemma 95.14.9: up to a replacement as in Remark 8.4.9, the functor
`p : G-Torsors ⟶ (Sch/S)_fppf` sending `(U, b, X)` to `U` is a stack in groupoids
over `(Sch/S)_fppf`. -/
@[stacks 04US] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.Torsors.instIsStackInGroupoids :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupAlgebraicSpace B},
      IsStack.InGroupoids (Scheme.fppfTopology.over S)
        (AlgebraicGeometry.GroupAlgebraicSpace.Torsors.forget G))

/- The fiberwise essential smallness supplies the size condition of
Remark 8.4.9 for the replacement. -/
#check (AlgebraicGeometry.GroupAlgebraicSpace.Torsors.fibers_essentiallySmall :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (U : Over S),
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty
        ((AlgebraicGeometry.GroupAlgebraicSpace.Torsors.forget G).Fiber U)))
