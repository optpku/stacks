/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 39.3.3: the restriction of a pre-relation on `U` over `S` along
`g : U' ⟶ U` is its pullback in the slice category. -/
@[stacks 02V9] #check
  (@AlgebraicGeometry.Scheme.PreRelation.pullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U U' : Over S}
      (P : AlgebraicGeometry.Scheme.PreRelation U) (g : U' ⟶ U),
        AlgebraicGeometry.Scheme.PreRelation U')

/- The source of the restricted pre-relation is the slice pullback of the original
source over the canonical map `U' ⨯ U' ⟶ U ⨯ U`. -/
#check
  (@AlgebraicGeometry.Scheme.PreRelation.pullback_left :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U U' : Over S}
      (P : AlgebraicGeometry.Scheme.PreRelation U) (g : U' ⟶ U),
        (P.pullback g).left =
          CategoryTheory.Limits.pullback P.hom (CategoryTheory.Limits.prod.map g g))

/- Its defining map is the second projection from that slice pullback. -/
#check
  (@AlgebraicGeometry.Scheme.PreRelation.pullback_hom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U U' : Over S}
      (P : AlgebraicGeometry.Scheme.PreRelation U) (g : U' ⟶ U),
        (P.pullback g).hom = CategoryTheory.Limits.pullback.snd P.hom
          (CategoryTheory.Limits.prod.map g g))
