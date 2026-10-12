/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Limit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.23.3

The reusable statement is owned by `RingedSite.Hom.modulePushforwardDerived` with independent
source, target, coefficient, and structure-sheaf universes.
-/

/- Lemma 21.23.3 (0A07): derived direct image commutes with sequential derived limits. -/
@[stacks 0A07] #check
  @RingedSite.Hom.modulePushforwardDerived.preservesDerivedLimit
