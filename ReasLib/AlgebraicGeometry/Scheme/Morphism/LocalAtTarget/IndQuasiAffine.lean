/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiAffine

/-!
# Ind-quasi-affine morphisms local on the target

Ind-quasi-affineness of scheme morphisms is local on the target for the fpqc
precoverage.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IndQuasiAffineHom

/-- Ind-quasi-affineness of scheme morphisms is local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@IndQuasiAffineHom : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IndQuasiAffineHom
