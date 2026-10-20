/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Limit

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.moduleDerivedPushforward

/-
Lemma 20.37.2: derived pushforward along a morphism of ringed spaces preserves sequential derived
limits.  The reusable owner returns `Nonempty (IsDerivedLimit ...)`, since an
`IsDerivedLimit` value contains a choice of Milnor presentation; the mathematical assertion is
existence of such a presentation, not a new canonical choice.
-/

@[stacks 0BKP "Lemma 20.37.2: derived pushforward preserves sequential derived limits"]
#check @preservesDerivedLimit

end
