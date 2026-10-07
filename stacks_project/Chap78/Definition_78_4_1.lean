module

import stacks_project.Chap78.Definition_78_4_1_PreRelation
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
variable (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)

/- Definition 78.4.1 (1): a pre-relation on `U` over `B` is an object over `U ⨯ U`
in `Over B`. -/
@[stacks 043C] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation U : Type (u + 1))

/- Definition 78.4.1 (2): a relation on `U` over `B` is a monomorphism into `U ⨯ U`
in `Over B`. -/
@[stacks 043C] #check
  (AlgebraicGeometry.AlgebraicSpace.Relation U : Type (u + 1))

/- Definition 78.4.1 (3): a pre-equivalence relation induces an equivalence relation on
the `T`-valued points of `U` for every scheme `T` over `B`. -/
@[stacks 043C] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsPreEquivalence P : Prop)

/- Definition 78.4.1 (4): an equivalence relation has an injective point map and an
equivalence-relation image for every scheme `T` over `B`. -/
@[stacks 043C] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsEquivalence P : Prop)
