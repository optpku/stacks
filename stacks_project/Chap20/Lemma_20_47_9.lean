/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Cohomology
import StacksCheckRecall

@[expose] public section

/- Lemma 20.47.9: the highest potentially nonzero cohomology sheaves of an
`m`-pseudo-coherent derived module satisfy finite-type and finite-presentation bounds. -/

@[stacks 08DN "(1)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.topCohomology_isFiniteType

@[stacks 08DN "(2)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.nextCohomology_isFinitePresentation

-- The same result is owned more generally for bundled ringed sites.
#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.topCohomology_isFiniteType

