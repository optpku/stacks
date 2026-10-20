/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RelativeCycle.ClosedSubscheme.Flat

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 62.6.8: in the situation of Example 62.5.4, if `S` is locally Noetherian
and `Z` is flat over `S` in dimensions `≥ r`, then the associated fibrewise
family `closedSubschemeFiberCycleFamily f Z r hZ` is a relative `r`-cycle on
`X / S`. -/
@[stacks 0H57] #check
  (AlgebraicGeometry.Scheme.Hom.closedSubschemeFiberCycleFamily_isRelative :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
      (Z : X.IdealSheafData) (r : ℕ)
      (hZ : f.fiberClosedSubschemeDimensionLE Z r)
      (hflat : f.closedSubschemeFlatOverInDimensionsGE Z r),
      RelativeCycle.IsRelative (Scheme.Hom.closedSubschemeFiberCycleFamily f Z r hZ))
