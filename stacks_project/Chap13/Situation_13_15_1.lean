/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Inclusion
import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Inclusion
import StacksCheckRecall

@[expose] public section

/-!
# Situation 13.15.1

The generic one-sided bounded homotopy-to-derived functors are owned by the `Above` and `Below`
leaves of `ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded`. This source entry is a recall
facade; it does not import the unrelated two-sided or composition layers.
-/

open CategoryTheory

/- Situation 13.15.1 (Stacks 05T4): an additive functor induces the unbounded,
bounded-below, and bounded-above homotopy-to-derived functors owned by `Functor`. -/
@[stacks 05T4]
#check @Functor.Homotopy.toDerived

@[stacks 05T4]
#check @Functor.toBoundedBelowDerived

@[stacks 05T4]
#check @Functor.toBoundedAboveDerived

@[stacks 05T4]
#check @Functor.toBoundedBelowDerived.compInclusionIso

@[stacks 05T4]
#check @Functor.toBoundedAboveDerived.compInclusionIso
