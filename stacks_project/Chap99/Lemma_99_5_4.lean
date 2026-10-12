/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import stacks_project.Chap99.Situation_99_5_1_Category

/-!
# Lemma 99.5.4

In Situation 99.5.1 the functor `p : Coh_{X/B} ⟶ (Sch/S)_fppf` is a stack in
groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.5.4: in Situation 99.5.1, with `f : X ⟶ B` of finite presentation,
the projection `p : CohStack f ⟶ Over S`, `(T, g, F) ↦ T`, is a stack in
groupoids over `(Sch/S)_fppf`. Hom-types of `Obj f` live in `Type (u + 1)`, so
this cannot land in `GroupoidsOver S`. -/
@[stacks 08KC]
instance instIsStackInGroupoids (f : X ⟶ B) [FinitePresentation f] :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p f) := sorry

/-- The projection `p f` is a stack on the site `(Sch/S)_fppf`. -/
theorem p_isStackOnSite (f : X ⟶ B) [FinitePresentation f] :
    IsStack.OnSite (Scheme.fppfTopology.over S) (p f) := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
