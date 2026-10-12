/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FormalFiber.Maximal
import StacksCheckRecall

/-!
# Lemma 15.51.4

@stack 0BIU
-/

@[expose] public section

/- Lemma 15.51.4, tag `0BIU`: for a property stable under regular-fiber ascent and faithfully
flat descent, the `P`-ring condition is detected at maximal localizations. -/
@[stacks 0BIU "maximal-local criterion for P-rings"]
#check @IsPRing.iff_forall_maximal_holdsOnFormalFibers

/- The localized form identifies the `P`-ring condition at a maximal ideal with the formal
fibers of that same local ring. -/
#check @IsPRing.localizationAtMaximal_iff_holdsOnFormalFibers

/- The underlying formal fibers can be reindexed by primes below the chosen maximal ideal. -/
#check @FieldAlgebraProperty.holdsOnFormalFibers_localizationAtPrime_iff
