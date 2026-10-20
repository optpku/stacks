module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 103.14.1 (1): let `X` be an algebraic stack. The lisse-étale site
of `X` is the Grothendieck topology `lisseEtaleTopology X` on the full
subcategory `lisseEtaleSite X` of `X` whose objects are those `x` lying over a
scheme `U` such that `yonedaHom X x : GroupoidsOver.slice U ⟶ X` is smooth. A covering is a
family of morphisms `{x_i ⟶ x}` of `lisseEtaleSite X` which forms a covering
for `X.etaleTopology`. -/
@[stacks 0787] #check (AlgebraicGeometry.AlgebraicStack.lisseEtaleTopology :
  {S : AlgebraicGeometry.Scheme.{u}} → (X : AlgebraicGeometry.GroupoidsOver S) →
    [AlgebraicGeometry.AlgebraicStack X] →
    CategoryTheory.GrothendieckTopology (AlgebraicGeometry.AlgebraicStack.lisseEtaleSite X))

/- Definition 103.14.1 (2): let `X` be an algebraic stack. The flat-fppf site of
`X` is the Grothendieck topology `flatFppfTopology X` on the full subcategory
`flatFppfSite X` of `X` whose objects are those `x` lying over a scheme `U` such
that `yonedaHom X x : GroupoidsOver.slice U ⟶ X` is flat. A covering is a family of morphisms
`{x_i ⟶ x}` of `flatFppfSite X` which forms a covering for `X.fppfTopology`. -/
@[stacks 0787] #check (AlgebraicGeometry.AlgebraicStack.flatFppfTopology :
  {S : AlgebraicGeometry.Scheme.{u}} → (X : AlgebraicGeometry.GroupoidsOver S) →
    [AlgebraicGeometry.AlgebraicStack X] →
    CategoryTheory.GrothendieckTopology (AlgebraicGeometry.AlgebraicStack.flatFppfSite X))
