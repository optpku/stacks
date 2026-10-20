module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.30.6: a syntomic morphism is locally of finite presentation. -/
@[stacks 01UK] #check (AlgebraicGeometry.Syntomic.locallyOfFinitePresentation :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S}, AlgebraicGeometry.Syntomic f →
      AlgebraicGeometry.LocallyOfFinitePresentation f)
