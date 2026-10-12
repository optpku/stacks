/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.Truncation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.23.8

The reusable owner is the generic truncation-comparison criterion with the canonical basiswise
negative-degree predicate.
-/

open RingedSite.Hom.ModuleDerived.Limit

/- Lemma 21.23.8 (0D6N): a compatible lower-truncation comparison is an isomorphism under
basiswise negative-degree cohomology-sheaf vanishing. -/
@[stacks 0D6N]
#check @Comparison.isIso_of_negative

#check @Basis.negative
#check @Basis.negative.toEventual
