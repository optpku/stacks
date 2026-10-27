/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Affine

/-!
# Affine étale charts of blowups

The canonical comparison identifies an affine étale base change of a blowup with
the Rees projective spectrum over the chart. Affine blowup algebras cover this fibre product.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Blowup

universe u

/- Lemma 71.17.2 (1): the canonical Rees comparison is an isomorphism. -/
@[stacks 085R] #check
  (AlgebraicGeometry.AlgebraicSpace.Blowup.affineComparisonHom_isIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
      [IsQuasiCoherent I] (π : Blowup X I) (U : affineEtaleSite X),
      IsIso (affineComparisonHom π U))

-- The comparison commutes with the structure morphism to the affine chart.
#check (AlgebraicGeometry.AlgebraicSpace.Blowup.affineComparisonHom_over :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] (π : Blowup X I) (U : affineEtaleSite X),
    affineComparisonHom π U ≫ reesProjOverToU I U = pullback.fst U.obj.hom π.hom)

/- Lemma 71.17.2 (2): spectra of affine blowup algebras cover the fibre product. -/
@[stacks 085R] #check
  (AlgebraicGeometry.AlgebraicSpace.Blowup.existsAffineOpenCoverByBlowupCharts :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
      [IsQuasiCoherent I] (π : Blowup X I) (U : affineEtaleSite X),
      IsZariskiCover (pullback U.obj.hom π.hom)
        (fun a : correspondingIdeal I U ↦
          ofOver (Over.mk (affineChartToU I U a ≫ U.obj.left.hom)))
        (fun a ↦ ofOverMap (affineChartOverHom I U a) ≫ inv (affineComparisonHom π U)))
