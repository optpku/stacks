module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.GeometricQuotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Definition 83.10.1: for `S` a scheme, `B` an algebraic space over `S`, and a pre-relation
`j : R ⟶ U ⨯ U` on an algebraic space `U` over `B`, a morphism `φ : U ⟶ X` of algebraic spaces
over `B` is a geometric quotient if `φ` is an orbit space, condition (1) holds universally,
i.e. `φ` is universally submersive, and the functions on `X` are the `R`-invariant functions
on `U`. -/
@[stacks 04AE] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsGeometricQuotient :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B},
    PreRelation U → (U ⟶ X) → Prop)
