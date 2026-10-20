/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import StacksCheckRecall

@[expose] public section


universe v vI uI

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] [Small.{v} I] [IsFiltered I]

/-
The verified comparison instance `colimitLimitToLimitColimit_isIso` directly handles a finite
category followed by a filtered category, while `filtered_colim_preservesFiniteLimits_of_types`
provides the canonical owner property below. The owner formulation avoids choosing an ordering of
the two factors: applying it to the curried form of `M : I × J ⥤ Type v` recovers the displayed
comparison after swapping the factors. It introduces no extra mathematical generality, includes
the stated product, pullback, and equalizer consequences, and lets downstream code use the usual
finite-limit preservation API.
-/

/- Lemma 4.19.2: for a filtered index category `I`, the colimit functor on `Type`-valued diagrams
preserves finite limits; equivalently, filtered colimits of sets commute with finite limits, in
particular with finite products, pullbacks, and equalizers. -/
@[stacks 002W "filtered colimits of sets commute with finite limits"]
#check (inferInstance : PreservesFiniteLimits (colim : (I ⥤ Type v) ⥤ Type v))

end CategoryTheory.Limits
