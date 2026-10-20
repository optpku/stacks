module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalScheme.Scheme

universe u

open CategoryTheory

/- 87.2.0.2: the comparison functor sends a scheme to the same underlying space and
structure-sheaf rings, with the pseudo-discrete topology on sections. -/
@[stacks 0AI0] #check (AlgebraicGeometry.Scheme.toFormalScheme.{u} :
  AlgebraicGeometry.Scheme.{u} ⥤ AlgebraicGeometry.FormalScheme.{u})
