module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Flat
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.30.7: a syntomic morphism is flat. -/
@[stacks 01UL] #check (AlgebraicGeometry.Syntomic.flat :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}, AlgebraicGeometry.Syntomic f → AlgebraicGeometry.Flat f)
