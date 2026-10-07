module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.AdditiveGroup

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry CategoryTheory.MonObj

universe u

/- Example 78.7.3 (Additive group algebraic space) (1): for every algebraic space `B` over
a scheme `S`, the additive group over `B` is a commutative group object in `Over B`. -/
@[stacks 043L] #check
  (AlgebraicGeometry.AlgebraicSpace.AdditiveGroup.commGroupSpace :
    {S : Scheme.{u}} → (B : AlgebraicSpace S) → CommGrp (Over B))

/- Example 78.7.3 (Additive group algebraic space) (2): the representing object is
`B ×_S 𝔾ₐ[S]`, with the first projection as its structure morphism to `B`. -/
@[stacks 043L] #check
  (AlgebraicGeometry.AlgebraicSpace.AdditiveGroup.groupSpace_spec :
    ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
      (AlgebraicGeometry.AlgebraicSpace.AdditiveGroup.groupSpace B).left.functorOfPoints =
          (B.functorOfPoints ⨯ yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X) ∧
        (AlgebraicGeometry.AlgebraicSpace.AdditiveGroup.groupSpace B).hom =
          (prod.fst : B.functorOfPoints ⨯
            yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X ⟶ B.functorOfPoints))

/- Example 78.7.3 (Additive group algebraic space) (3): its points on every scheme over `B`
are group-isomorphic to the additive global sections of that scheme. -/
@[stacks 043L] #check
  (AlgebraicGeometry.AlgebraicSpace.AdditiveGroup.homMulEquiv :
    {S : Scheme.{u}} → (B : AlgebraicSpace S) → (T : Over S) →
      (baseMap : ofOver T ⟶ B) →
        (Over.mk baseMap ⟶ AlgebraicGeometry.AlgebraicSpace.AdditiveGroup.groupSpace B) ≃*
          Multiplicative Γ(T.left, ⊤))

/- Example 78.7.3 (Additive group algebraic space) (4): this representation is natural;
precomposition of points along schemes over `B` corresponds to pullback of sections. -/
@[stacks 043L] #check
  (AlgebraicGeometry.AlgebraicSpace.AdditiveGroup.homMulEquiv_naturality :
    ∀ {S : Scheme.{u}} (B : AlgebraicSpace S) (T T' : Over S)
      (baseMap : ofOver T ⟶ B) (baseMap' : ofOver T' ⟶ B) (testMap : T' ⟶ T)
      (h_over : yoneda.map testMap ≫ baseMap = baseMap')
      (point : Over.mk baseMap ⟶ AlgebraicGeometry.AlgebraicSpace.AdditiveGroup.groupSpace B),
      AlgebraicGeometry.AlgebraicSpace.AdditiveGroup.homMulEquiv B T' baseMap'
          (Over.homMk (V := Over.mk baseMap)
            (yoneda.map testMap : ofOver T' ⟶ ofOver T) h_over ≫ point) =
        Multiplicative.ofAdd (testMap.left.appTop (Multiplicative.toAdd
          (AlgebraicGeometry.AlgebraicSpace.AdditiveGroup.homMulEquiv B T baseMap point))))
