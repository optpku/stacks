/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.KInjective

/-!
# Lemma 15.56.3

@stack 0917
-/

@[expose] public section

/- Lemma 15.56.3 (0917): coextension of scalars along a ring map preserves K-injective
cochain complexes. -/
@[stacks 0917]
#check @ModuleCat.CoextendScalars.isKInjective

#check @CochainComplex.IsKInjective.mapHomologicalComplex_of_exactLeftAdjoint
#check @ModuleCat.restrictScalars_exact
