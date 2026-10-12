/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Pullback
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 78.4.3: the restriction, or pullback, of a pre-relation on `U`
over `B` along `g : U' ⟶ U` is `PreRelation.pullback`; the source sometimes
writes `R' = R|_{U'}`. -/
@[stacks 043E] #check
  (@AlgebraicGeometry.AlgebraicSpace.PreRelation.pullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
      {U U' : Over B}, AlgebraicGeometry.AlgebraicSpace.PreRelation U → (U' ⟶ U) →
        AlgebraicGeometry.AlgebraicSpace.PreRelation U')

/- The source of the restricted pre-relation is the slice pullback of the original
source over the canonical map `U' ⨯ U' ⟶ U ⨯ U`. -/
#check
  (@AlgebraicGeometry.AlgebraicSpace.PreRelation.pullback_left :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
      {U U' : Over B} (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
      (g : U' ⟶ U),
        (P.pullback g).left =
          CategoryTheory.Limits.pullback P.hom (CategoryTheory.Limits.prod.map g g))

/- Its defining map is the second projection from that slice pullback. -/
#check
  (@AlgebraicGeometry.AlgebraicSpace.PreRelation.pullback_hom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
      {U U' : Over B} (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
      (g : U' ⟶ U),
        (P.pullback g).hom = CategoryTheory.Limits.pullback.snd P.hom
          (CategoryTheory.Limits.prod.map g g))
