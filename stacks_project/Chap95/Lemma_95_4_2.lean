/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap95.«95_4_0_1_Category»
public import ReasLib.CategoryTheory.Fibered.Stack.Over.Projection
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Lemma 95.4.2

The functor `p : QCohStack ⥤ (Sch/S)_fppf` satisfies conditions (1), (2) and
(3) of Stacks Definition 8.4.1: it is fibered, Hom-presheaves of restrictions
are sheaves, and descent data for fppf coverings are effective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.QCohStack

/-- Lemma 95.4.2: the functor `p : QCohStack ⥤ (Sch/S)_fppf` satisfies
conditions (1), (2) and (3) of Stacks Definition 8.4.1. -/
@[stacks 03YM, instance]
instance instIsStackOnSite (S : Scheme.{u}) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (p S) :=
  sorry

/-- The stack of quasi-coherent sheaves over `(Sch/S)_fppf`. -/
abbrev stack (S : Scheme.{u}) : StackOver (Scheme.fppfTopology.over S) :=
  StackOver.ofProjection (Scheme.fppfTopology.over S) (p S)

/-- The projection of `stack S` is the functor `p S`. -/
theorem stack_p (S : Scheme.{u}) : (stack S).p = p S :=
  sorry

end AlgebraicGeometry.QCohStack
