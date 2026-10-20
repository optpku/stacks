/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- The associativity of a relative cup product is not a theorem about an arbitrary pointwise
tensor comparison.  It is the associativity law of the canonical lax monoidal structure on the
right adjoint, whose hypotheses include the required oplax coherence on the left adjoint. -/

#check @Adjunction.rightAdjointLaxMonoidal
#check @Functor.LaxMonoidal.μ
#check @Functor.LaxMonoidal.associativity
