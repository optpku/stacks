/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings.KInjective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.20.11

Same-site coextension of scalars preserves K-injective complexes because its left adjoint,
restriction of scalars, is exact.
-/

/- Lemma 21.20.11 (093Z): coextension of scalars along a morphism of ring sheaves preserves
K-injective cochain complexes. -/
@[stacks 093Z]
#check @SheafOfModules.RingedSite.coextendAlong.mapComplex_isKInjective

#check @SheafOfModules.RingedSite.restrictionAlong_exact
#check @CochainComplex.IsKInjective.mapHomologicalComplex_of_exactLeftAdjoint
