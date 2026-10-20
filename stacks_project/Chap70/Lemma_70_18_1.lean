module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.Over.OpenGluing

@[expose] public section

open CategoryTheory

universe u

/- Lemma 70.18.1. For a scheme covered by two opens, base change induces an
 equivalence on the categories of algebraic spaces of finite presentation. -/
@[stacks 0E8Z] #check
  (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.glueFunctor_isEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (U W : S.Opens), U ⊔ W = ⊤ →
      (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.glueFunctor U W).IsEquivalence)
