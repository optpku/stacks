/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_56_1_ResidueGalois
import StacksCheckRecall

open AlgebraicGeometry

@[expose] public section

/- Definition 59.56.1 (1): the separable closure of the residue field inside
the source field of a geometric point. -/
@[stacks 03QX] #check Scheme.GeometricPoint.separableClosure

/- Definition 59.56.1 (2): the absolute Galois group of the residue field is
Gal of the point-specific separable closure. -/
@[stacks 03QX] #check Scheme.GeometricPoint.absoluteGaloisGroup

/- Definition 59.56.1 (3): a geometric point is algebraic when its source field
is an algebraic closure of the residue field at its image. -/
@[stacks 03QX] #check Scheme.GeometricPoint.IsAlgebraic
