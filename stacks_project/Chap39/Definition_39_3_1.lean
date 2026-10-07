module

import ReasLib.AlgebraicGeometry.Scheme.PreRelation
import StacksCheckRecall

open CategoryTheory

universe u

variable {S : AlgebraicGeometry.Scheme.{u}} {U : Over S}
variable (P : AlgebraicGeometry.Scheme.PreRelation U)

/- Definition 39.3.1 (1): a pre-relation on `U` over `S` is an object over `U ⨯ U`
in `Over S`. -/
@[stacks 022P] #check
  (AlgebraicGeometry.Scheme.PreRelation U : Type (u + 1))

/- Definition 39.3.1 (2): a relation on `U` over `S` is a monomorphism into `U ⨯ U`
in `Over S`. -/
@[stacks 022P] #check
  (AlgebraicGeometry.Scheme.Relation U : Type (u + 1))

/- Definition 39.3.1 (3): a pre-equivalence relation induces an equivalence relation on
the `T/S`-valued points of `U` for every `T : Over S`. -/
@[stacks 022P] #check
  (AlgebraicGeometry.Scheme.PreRelation.IsPreEquivalence P : Prop)

/- Definition 39.3.1 (4): an equivalence relation is characterized by injectivity of the
point map and by the equivalence-relation property of the induced image relation for every
`T : Over S`. -/
@[stacks 022P] #check
  (AlgebraicGeometry.Scheme.PreRelation.isEquivalenceRelation_iff_points P :
    IsEquivalenceRelation
        (AlgebraicGeometry.Scheme.PreRelation.t P)
        (AlgebraicGeometry.Scheme.PreRelation.s P) ↔
      ∀ T : Over S,
        Function.Injective (AlgebraicGeometry.Scheme.PreRelation.pointMap P T) ∧
          Equivalence (AlgebraicGeometry.Scheme.PreRelation.pointRel P T))
