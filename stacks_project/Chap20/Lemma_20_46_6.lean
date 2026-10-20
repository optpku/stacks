/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.StrictlyPerfect.LocalHomotopy
import StacksCheckRecall

@[expose] public section

/- Lemma 20.46.6: a strictly perfect complex maps locally null-homotopically into an acyclic
complex, and the same conclusion holds under the bounded-below homology-vanishing hypothesis.
The reusable owner is the ringed-space `CochainComplex.IsStrictlyPerfect.NullHomotopy` namespace;
its `cover` and `at` views expose both the open-cover and point-neighborhood formulations. -/

@[stacks 08C7 "(1) open-cover view"]
#check
  @AlgebraicGeometry.RingedSpace.CochainComplex.IsStrictlyPerfect.NullHomotopy.cover_of_acyclic

@[stacks 08C7 "(1) point-neighborhood view"]
#check
  @AlgebraicGeometry.RingedSpace.CochainComplex.IsStrictlyPerfect.NullHomotopy.at_of_acyclic

@[stacks 08C7 "(2) open-cover view"]
#check
  @AlgebraicGeometry.RingedSpace.CochainComplex.IsStrictlyPerfect.NullHomotopy.cover_of_isStrictlyGE

@[stacks 08C7 "(2) point-neighborhood view"]
#check
  @AlgebraicGeometry.RingedSpace.CochainComplex.IsStrictlyPerfect.NullHomotopy.at_of_isStrictlyGE

#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsNullHomotopicOn
#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyNullHomotopicAt
