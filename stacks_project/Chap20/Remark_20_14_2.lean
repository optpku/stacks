/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Lifting
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward.Bounded
import StacksCheckRecall

@[expose] public section

/-!
# Computing the derived cohomology map with injective resolutions

The chosen map between injective resolutions is proof-level computation of the canonical
change-of-space map.  It is supplied by the general lifting API and does not define a second
public map depending on resolution choices.
-/

/- Remark 20.14.2: the canonical derived global-sections map of an `f`-map can be represented by a
strictly commuting lift between chosen bounded-below injective resolutions. -/
@[stacks 01FB]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Bounded.mapOfFMap

/- The comparison morphism between resolutions is an instance of the generic strict lifting
theorem into a bounded-below complex of injectives. -/
#check @CochainComplex.InjectivePlus.exists_lift_of_termwiseMono

/- The vertical quasi-isomorphism in the computation is the derived sections/direct-image
comparison from Lemma 20.13.1. -/
#check @AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Bounded.pushforwardIso
