module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme

universe u

variable (S : AlgebraicGeometry.Scheme.{u})

/- Definition 39.4.1: Group schemes over `S`, together with their homomorphisms,
are the internal group objects in the category of schemes over `S`. -/
@[stacks 022S] #check (AlgebraicGeometry.GroupScheme S : Type (u + 1))
