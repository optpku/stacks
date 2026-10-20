/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Graded
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Construction

/-!
# Affine cones from graded quasi-coherent algebras

This file defines the affine cone of an explicitly graded quasi-coherent algebra using a chosen
relative-spectrum model of its underlying algebra.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- The affine cone of a graded quasi-coherent algebra, formed from an explicit valid chosen
relative-spectrum model of its underlying algebra. -/
def affineCone (A : GradedQcAlgebra S) (P : RelativeSpectrumOver A.algebra)
    [IsRelativeSpectrumOver P] : Scheme.{u} :=
  relativeSpec P

/-- The affine cone is the scheme underlying its chosen relative-spectrum model. -/
theorem affineCone_eq_relativeSpec (A : GradedQcAlgebra S)
    (P : RelativeSpectrumOver A.algebra) [IsRelativeSpectrumOver P] :
    affineCone A P = relativeSpec P :=
  rfl

end AlgebraicGeometry.Scheme
