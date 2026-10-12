/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import stacks_project.Chap95.Lemma_95_14_10_Torsors

/-!
# Lemma 95.14.9

The functor `p : G-Torsors ⟶ (Sch/S)_fppf` is a stack in groupoids, up to the
small-fiber replacement of Remark 8.4.9.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Torsors

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- Lemma 95.14.9: up to a replacement as in Remark 8.4.9, the functor
`p : G-Torsors ⟶ (Sch/S)_fppf` sending `(U, b, X)` to `U` is a stack in groupoids
over `(Sch/S)_fppf`. -/
@[stacks 04US]
instance isStackInGroupoids (G : GroupAlgebraicSpace B) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget G) := sorry

/-- Remark 8.4.9 condition (4): the fibre of `G`-Torsors over `U` is essentially
small, so a small model exists via `StackOver.SmallModel`. -/
theorem fibers_essentiallySmall (G : GroupAlgebraicSpace B) (U : Over S) :
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((forget G).Fiber U)) := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Torsors
