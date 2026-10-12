/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Remark_106_6_1_Category_of_lifts_Category
public import ReasLib.CategoryTheory.Fibered.Gerbe.Basic

/-!
# The category of lifts is a gerbe
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

/-- Lemma 106.6.7: the functor `p iX x : Object iX x ⥤ AlgebraicSpace.spacesEtaleSite W`
constructed in Remark 106.6.1 is a gerbe on the spaces-étale site of `W`. -/
@[stacks 0CJX]
instance instIsGerbe {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
    {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] :
    CategoryTheory.IsGerbe (AlgebraicSpace.spacesEtaleTopology W) (p iX x) := sorry

end AlgebraicGeometry.AlgebraicStack.Lift
