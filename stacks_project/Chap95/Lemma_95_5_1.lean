/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap95.Lemma_95_5_1_Category
public import ReasLib.CategoryTheory.Fibered.Stack.Over.Projection
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Lemma 95.5.1

The functor `p_fg : QCoh_fg ⥤ (Sch/S)_fppf` satisfies conditions (1), (2) and
(3) of Stacks Definition 8.4.1: it is a stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.QCohStack.FG

/-- Lemma 95.5.1: the functor `p_fg : QCoh_fg ⥤ (Sch/S)_fppf` satisfies
conditions (1), (2) and (3) of Stacks Definition 8.4.1. -/
@[stacks 04U4, instance]
instance instIsStackOnSite (S : Scheme.{u}) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (p S) :=
  sorry

/-- The stack of finite-type quasi-coherent sheaves over `(Sch/S)_fppf`. -/
abbrev stack (S : Scheme.{u}) : StackOver (Scheme.fppfTopology.over S) :=
  StackOver.ofProjection (Scheme.fppfTopology.over S) (p S)

/-- The projection of `stack S` is the functor `p S`. -/
theorem stack_p (S : Scheme.{u}) : (stack S).p = p S :=
  sorry

end AlgebraicGeometry.QCohStack.FG
