module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic.FinitePresentation
import StacksCheckRecall

/-!
# Syntomic morphisms of algebraic spaces are locally of finite presentation
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.36.5: A syntomic morphism is locally of finite presentation. -/
@[stacks 0DEY] #check (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_of_syntomic :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.Syntomic f],
      AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f)
