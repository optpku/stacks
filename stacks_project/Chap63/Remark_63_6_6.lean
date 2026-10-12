/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Remark_63_6_6_Forgetful
public import stacks_project.Chap63.Remark_63_6_6_Shriek
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

/- Remark 63.6.6 (1): a locally quasi-finite morphism `f : X ⟶ Y` induces an
adjoint pair `pointedLowerShriek f ⊣ pointedUpperShriek f` on sheaves of pointed
sets `Sheaf (smallEtaleTopology _) Pointed`. -/
@[stacks 0F5L]
#check pointedLowerShriekAdjunction

/- Remark 63.6.6 (2): the stalk of `pointedLowerShriek f` at a geometric point
`ybar` of `Y` is the coproduct in `Pointed` of the stalks of the sheaf at
geometric points of `X` over `ybar`, naturally in the pointed sheaf. -/
@[stacks 0F5L]
#check pointedLowerShriekStalkIso

/- Remark 63.6.6 (3): `pointedUpperShriek f` of a skyscraper sheaf at `ybar` is
the product of skyscrapers at geometric points of `X` over `ybar`, naturally
in the pointed set. -/
@[stacks 0F5L]
#check pointedUpperShriekSkyscraperIso

/- Remark 63.6.6 (4): compatibility with the forgetful functors
`etaleForgetfulPointed` produces a canonical comparison
`etaleForgetfulPointed X ⋙ pointedLowerShriek f ⟶ lowerShriek f ⋙ etaleForgetfulPointed Y`
inducing `toPointedCoprodComparison` on stalks. -/
@[stacks 0F5L]
#check forgetfulLowerShriekComparison

/- Remark 63.6.6 (5): compatibility produces a canonical comparison
`F ∘ f^! ⟶ f^! ∘ F`, the mate of `forgetfulLowerShriekComparison` along a
right adjoint of `lowerShriek f`. -/
@[stacks 0F5L]
#check forgetfulUpperShriekComparison

/- Remark 63.6.6 (6): the transformation `F ∘ f^! ⟶ f^! ∘ F` is an isomorphism
because this mate of the lower comparison commutes with products. -/
@[stacks 0F5L]
#check forgetfulUpperShriekComparison_isIso

end
