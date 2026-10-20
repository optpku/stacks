module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.ValuativeCriterion
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.4.3: for a proper morphism of finite presentation, the structure
morphism of the stack of coherent sheaves satisfies the existence part of the
valuative criterion. -/
@[stacks 0DM0] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.instExistence_forget :
  {S : Scheme.{u}} → {X B : AlgebraicSpace S} →
    (f : X ⟶ B) → [FinitePresentation f] → [Proper f] →
      AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.ValuativeCriterion.Existence
        (AlgebraicGeometry.AlgebraicSpace.CohStack.forget f))
