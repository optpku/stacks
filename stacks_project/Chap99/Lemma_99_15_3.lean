/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import stacks_project.Chap99.Lemma_99_15_2

/-!
# Lemma 99.15.3

The category Curves of families of curves is a stack in groupoids over
`Sch_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- Lemma 99.15.3: the category Curves of families of curves is a stack in
groupoids over `Sch_fppf`, via the forgetful functor `p S : Obj S ⥤ Over S`,
with `Over S` playing the role of `Sch_fppf`. Hom-types live in `Type (u + 1)`,
so this cannot land in `GroupoidsOver S`. -/
@[stacks 0D52]
instance instIsStackInGroupoids (S : Scheme.{u}) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p S) := sorry

/-- The projection `p S` is a stack on the site `(Sch/S)_fppf`. -/
theorem p_isStackOnSite (S : Scheme.{u}) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (p S) := sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
