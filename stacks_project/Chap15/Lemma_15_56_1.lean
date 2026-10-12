/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.KInjective
import StacksCheckRecall

/-!
# Lemma 15.56.1

@stack 0915
-/

@[expose] public section

/- Lemma 15.56.1 (0915): a K-injective cochain complex remains K-injective after restriction of
scalars along a flat ring map. -/
@[stacks 0915] #check @ModuleCat.RestrictScalars.isKInjective_of_flat

/- Generic owner: right adjoints of exact functors preserve K-injective cochain complexes. -/
#check @CochainComplex.IsKInjective.mapHomologicalComplex_of_exactLeftAdjoint

/- Change-of-rings ingredients used by the reusable specialization. -/
#check @ModuleCat.extendRestrictScalarsAdj
#check @ModuleCat.extendScalars_exact_of_flat
