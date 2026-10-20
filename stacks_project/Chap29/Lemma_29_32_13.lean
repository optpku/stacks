module

import ReasLib.AlgebraicGeometry.Scheme.Differentials.FinitePresentation
import StacksCheckRecall

open scoped AlgebraicGeometry

universe u

/- Lemma 29.32.13: if a morphism of schemes is locally of finite presentation, then its relative
differential sheaf is a finitely presented module sheaf. -/
@[stacks 01V3] #check
  (AlgebraicGeometry.instIsFinitePresentationDifferentialsOfLocallyOfFinitePresentation :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFinitePresentation f],
      (Ω[f.toShHom]).IsFinitePresentation)
