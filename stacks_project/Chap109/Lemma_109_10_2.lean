/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.GeometricallyReduced
import StacksCheckRecall

/-!
# Geometrically reduced curves are Cohen–Macaulay

The geometrically reduced locus of the stack of curves is contained in the
Cohen–Macaulay locus. Both loci are packaged as object properties of families
of curves, matching the open substacks 𝒞urves^{geomred} and 𝒞urves^{CM}.
-/

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 109.10.2: we have 𝒞urves^{geomred} ⊂ 𝒞urves^{CM} as open substacks of 𝒞urves. -/
@[stacks 0E1G]
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.geometricallyReduced_le_cohenMacaulay :
  ∀ S : Scheme.{u},
    AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.geometricallyReduced S ≤
      AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.cohenMacaulay S)

#check (AlgebraicGeometry.Scheme.CohenMacaulay.of_isReduced_of_topologicalKrullDim_le_one :
  ∀ (X : Scheme.{u}) [IsReduced X] [IsLocallyNoetherian X],
    topologicalKrullDim X ≤ 1 → Scheme.CohenMacaulay X)
