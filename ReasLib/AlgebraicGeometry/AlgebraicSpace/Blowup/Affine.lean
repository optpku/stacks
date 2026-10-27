/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.ReesProj
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Comparison

/-!
# Affine étale charts of algebraic-space blowups

The canonical Rees comparison is invertible and transports affine blowup charts
to a Zariski covering of the fibre product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {I : IdealSubobject X} [IsQuasiCoherent I]

/-- The canonical comparison of an affine étale base change of a blowup with the
projective spectrum of its restricted Rees algebra is an isomorphism. -/
instance affineComparisonHom_isIso (π : Blowup X I) (U : affineEtaleSite X) :
    IsIso (affineComparisonHom π U) := sorry

/-- The fibre product of an affine étale chart with a blowup is covered by spectra
of the affine blowup algebras of its restricted section ideal. -/
theorem existsAffineOpenCoverByBlowupCharts (π : Blowup X I) (U : affineEtaleSite X) :
    IsZariskiCover (pullback U.obj.hom π.hom)
      (fun a : correspondingIdeal I U ↦
        ofOver (Over.mk (affineChartToU I U a ≫ U.obj.left.hom)))
      (fun a ↦ ofOverMap (affineChartOverHom I U a) ≫ inv (affineComparisonHom π U)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
