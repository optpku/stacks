/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_17_4_Relative

/-!
# Base change of relative property (β), decent, and reasonable morphisms

Having property (β), being decent, or being reasonable is preserved under arbitrary
base change of morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.17.4 (1): Having property (β) is preserved under arbitrary base change. -/
@[stacks 03L0]
instance propertyBeta_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@PropertyBeta S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Lemma 68.17.4 (2): Being decent is preserved under arbitrary base change. -/
@[stacks 03L0]
instance decent_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Decent S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Lemma 68.17.4 (3): Being reasonable is preserved under arbitrary base change. -/
@[stacks 03L0]
instance reasonable_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Reasonable S : MorphismProperty (AlgebraicSpace S)) := sorry

#check PropertyBeta.pullback_snd
#check Decent.pullback_snd
#check Reasonable.pullback_snd

end AlgebraicGeometry.AlgebraicSpace
