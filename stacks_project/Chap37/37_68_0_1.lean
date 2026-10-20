module

import ReasLib.AlgebraicGeometry.Scheme.RelativeHom.Morphism
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- 37.68.0.1: the displayed morphism b is a morphism in Over T.left between
the pullbacks T ×_S Z and T ×_S X, preserving their projections to T. -/
@[stacks 0BL1] #check
  (AlgebraicGeometry.Scheme.RelativeHom.BaseChangeMorphism :
    {S : Scheme.{u}} → (Z X T : Over S) → Type u)
