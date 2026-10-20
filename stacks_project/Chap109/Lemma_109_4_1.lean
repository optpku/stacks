/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PolarizedCurves.Immersion
import StacksCheckRecall

/- Lemma 109.4.1: the morphism PolarizedCurves ⟶ Polarized is an open and
closed immersion. -/
@[stacks 0DPZ] #check
  (AlgebraicGeometry.PolarizedCurves.inclusionHom_isOpenAndClosedImmersion :
    AlgebraicGeometry.Groupoids.Hom.OpenImmersion
        AlgebraicGeometry.PolarizedCurves.inclusionHom ∧
      AlgebraicGeometry.Groupoids.Hom.ClosedImmersion
        AlgebraicGeometry.PolarizedCurves.inclusionHom)
