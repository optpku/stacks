module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.RelativeDimension
import StacksCheckRecall

open CategoryTheory

universe u

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/- Definition 59.26.1: a morphism of schemes is étale exactly when it is
smooth of relative dimension 0. -/
@[stacks 03PB] #check (AlgebraicGeometry.Scheme.Hom.etale_iff_smoothOfRelativeDimension_zero f :
  AlgebraicGeometry.Etale f ↔ AlgebraicGeometry.SmoothOfRelativeDimension 0 f)
