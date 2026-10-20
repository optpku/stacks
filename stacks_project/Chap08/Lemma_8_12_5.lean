/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.12.5 (tag 04WF): under the stated finite-limit and preservation hypotheses, the
vertical strongly-cartesian denominator class admits a right calculus of fractions. The
definition, membership criterion, and multiplicativity instance are reusable prerequisites. -/
#check @Functor.pushforwardFractions
#check @Functor.pushforwardFractions.mem_iff
#check @Functor.pushforwardFractions.isMultiplicative
#check @Functor.Pushforward.sourceProjection.vertical_iff

@[stacks 04WF "pushforward fractions admit a right calculus"]
#check @Functor.pushforwardFractions.hasRightCalculus

#check @Functor.Pushforward.ProjectionChoice
#check @Functor.Pushforward.projection
#check @Functor.pushforwardProjection

end CategoryTheory
