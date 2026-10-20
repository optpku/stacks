/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Shift
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.14.5

The source shift statements are supplied by the neutral pointwise-derived shift API.  Its public
surface is independent of the Chapter 13 presentation: raw pointwise values, their shift
comparison isomorphisms, and the corresponding definedness transport.
-/

/- Lemma 13.14.5 (1): pointwise right-derived definedness is invariant under shift. -/
@[stacks 05SU]
#check @CategoryTheory.Functor.RightDerived.Value.Shift.hasPointwiseAt_iff_shift

/- Lemma 13.14.5 (2): a pointwise right-derived value commutes with shift up to its canonical
comparison isomorphism. -/
@[stacks 05SU]
#check @CategoryTheory.Functor.RightDerived.Value.Shift.valueIso

/- Lemma 13.14.5 (3): pointwise left-derived definedness is invariant under shift. -/
@[stacks 05SU]
#check @CategoryTheory.Functor.LeftDerived.Value.Shift.hasPointwiseAt_iff_shift

/- Lemma 13.14.5 (4): a pointwise left-derived value commutes with shift up to its canonical
comparison isomorphism. -/
@[stacks 05SU]
#check @CategoryTheory.Functor.LeftDerived.Value.Shift.valueIso
