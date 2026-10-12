/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import stacks_project.Chap99.Lemma_99_10_1_Picard

/-!
# Lemma 95.16.1

The functor `p : Pic_{X/B} ⟶ (Sch/S)_fppf` is a stack in groupoids, up to the
small-fiber replacement of Remark 8.4.9.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 95.16.1: up to a replacement as in Remark 8.4.9, the functor
`p : Pic_{X/B} ⟶ (Sch/S)_fppf` sending `(U, b, L)` to `U` is a stack in groupoids
over `(Sch/S)_fppf`. -/
@[stacks 04WN]
instance isStackInGroupoids (f : X ⟶ B) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p f) := sorry

/-- Remark 8.4.9 condition (4): the fibre of `Picard.p f` over `U` is essentially
small, so a small model exists via `StackOver.SmallModel`. -/
theorem fibers_essentiallySmall (f : X ⟶ B) (U : Over S) :
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((p f).Fiber U)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
