/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Operations
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.21.4 (1): the base change of a morphism which is locally of finite presentation is
locally of finite presentation. -/
@[stacks 01TS] #check
  (AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))

#check CategoryTheory.MorphismProperty.pullback_snd

/- Lemma 29.21.4 (2): the base change of a morphism of finite presentation is of finite
presentation. -/
@[stacks 01TS] #check
  (AlgebraicGeometry.Scheme.Hom.finitePresentation_pullback_snd :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S),
      Scheme.Hom.FinitePresentation f → Scheme.Hom.FinitePresentation (pullback.snd f g))
