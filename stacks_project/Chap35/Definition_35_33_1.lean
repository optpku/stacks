module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.EtaleLocal
import StacksCheckRecall

universe u

/- Definition 35.33.1: a property of morphisms of scheme germs is étale local on the
source-and-target when it is invariant across every commutative square with étale vertical
arrows. -/
@[stacks 04NB] #check (AlgebraicGeometry.Scheme.Germ.MorphismProperty.IsEtaleLocal :
  CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.Germ.{u} → Prop)
