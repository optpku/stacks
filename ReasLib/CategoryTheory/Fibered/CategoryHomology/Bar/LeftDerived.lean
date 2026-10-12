/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryHomology.Bar.DeltaFunctor
public import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective computation of fiber Bar homology

When the source sheaf category has projective resolutions, Mathlib's projective left-derived
functors provide a computational model for the resolution-independent universal delta functor in
`Bar.DeltaFunctor`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v wX vX w

namespace CategoryTheory.FiberedCategoryOver.FiberHomology.Bar

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (X : FiberedCategoryOver.{u, v, wX, vX} C)
variable [UnivLE.{max wX vX, w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasSheafify (X.p.inheritedTopology J) AddCommGrpCat.{w}]
variable [
  (X.p.sheafPushforwardContinuous AddCommGrpCat.{w}
    (X.p.inheritedTopology J) J).IsRightAdjoint]
variable [HasProjectiveResolutions
  (Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w})]

/-- Under projective resolutions, the left-derived projection lower shriek functor is computed by
fiber Bar homology. -/
@[stacks 08PJ "projective computation of derived projection lower shriek"]
theorem leftDerived_isomorphic (n : ℕ) :
    IsIsomorphic
      ((X.p.sheafPullback AddCommGrpCat.{w}
        (X.p.inheritedTopology J) J).leftDerived n)
      (sheafOfSheafFunctor J X n) := sorry

/-- Objectwise form of the projective computation of derived projection lower shriek. -/
@[stacks 08PJ "projective computation of derived projection lower shriek on an object"]
theorem leftDerived_obj_isomorphic
    (F : Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w}) (n : ℕ) :
    IsIsomorphic
      (((X.p.sheafPullback AddCommGrpCat.{w}
        (X.p.inheritedTopology J) J).leftDerived n).obj F)
      (sheafOfSheaf J X F n) := sorry

end CategoryTheory.FiberedCategoryOver.FiberHomology.Bar
