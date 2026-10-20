/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.StrictlyPerfect.LocalHomotopy
import StacksCheckRecall

@[expose] public section

/- Lemma 20.46.7: a map from a bounded-below strictly perfect complex lifts locally through a
homology isomorphism above the bound and an epimorphism in the boundary degree.  The reusable
owner is the symmetric `CochainComplex.IsStrictlyPerfect.Lift` namespace. -/

@[stacks 08C8 "open-cover view"]
#check
  @AlgebraicGeometry.RingedSpace.CochainComplex.IsStrictlyPerfect.Lift.cover_of_isStrictlyGE

@[stacks 08C8 "point-neighborhood view"]
#check
  @AlgebraicGeometry.RingedSpace.CochainComplex.IsStrictlyPerfect.Lift.at_of_isStrictlyGE

#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsLiftableOn
#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyLiftableAt
#check @RingedSite.CochainComplex.IsLocallyLiftableAt
