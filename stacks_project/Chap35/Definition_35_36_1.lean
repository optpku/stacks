module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty
import StacksCheckRecall

universe u

/- Definition 35.36.1: A property of morphisms of schemes satisfies descent for one of the
Zariski, fpqc, fppf, étale, smooth, or syntomic topologies when every descent datum on a
cover whose component structure morphisms have that property is effective. -/
@[stacks 02W2] #check (CategoryTheory.MorphismProperty.SatisfiesDescent :
  CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u} →
    AlgebraicGeometry.DescentTopology → Prop)
