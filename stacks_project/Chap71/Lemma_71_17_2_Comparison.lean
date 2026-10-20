/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap71.Lemma_71_17_2_PointMap

/-!
# Affine étale comparison morphisms for algebraic-space blowups

The forward comparison `U ×_X X' ⟶ Proj(⊕ I_A^d)` is assembled from Rees-ratio
charts in `Lemma_71_17_2_PointMap`. Chart inclusions into `reesProjOver` are
`Over.homMk` of `affineChartι`. An inverse classifying map of `reesProjOver`
into the blowup is not exported for a general affine étale chart, because
`Twist.localCoverHom` is typed only against the atlas local cover.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- The over-morphism of an affine blowup chart into `reesProjOver I U`. -/
def affineChartOverHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X)
    (a : correspondingIdeal I U) :
    Over.mk (affineChartToU I U a ≫ U.obj.left.hom) ⟶ reesProjOver I U :=
  Over.homMk (affineChartι I U a) sorry

/-- `affineChartOverHom` is `Over.homMk` of `affineChartι`. -/
theorem affineChartOverHom_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X)
    (a : correspondingIdeal I U) :
    (affineChartOverHom I U a).left = affineChartι I U a :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
