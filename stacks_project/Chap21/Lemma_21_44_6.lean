/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocalHomotopy
import StacksCheckRecall

@[expose] public section

/- Lemma 21.44.6 (1) (08FP): a morphism from a strictly perfect complex to an acyclic
complex is locally null-homotopic. -/
@[stacks 08FP "(1)"]
#check @RingedSite.CochainComplex.IsStrictlyPerfect.NullHomotopy.at_of_acyclic

/- Lemma 21.44.6 (2) (08FP): the same conclusion holds for a source bounded below by `a`
when the target homology vanishes in degrees at least `a`. -/
@[stacks 08FP "(2)"]
#check @RingedSite.CochainComplex.IsStrictlyPerfect.NullHomotopy.at_of_isStrictlyGE
