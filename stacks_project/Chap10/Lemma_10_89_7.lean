/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler.Exact
import StacksCheckRecall

/-!
# Lemma 10.89.7

@stack 059N
-/

@[expose] public section

/- Chap10 Lemma 10 89 7 (1): a universally exact submodule of a Mittag-Leffler module is
Mittag-Leffler. -/
@[stacks 059N "(1)"]
#check @CategoryTheory.ShortComplex.UniversallyExact.mittagLeffler_X₁

/- Chap10 Lemma 10 89 7 (2): in a universally exact short complex, Mittag-Leffler endpoints
force the middle term to be Mittag-Leffler. -/
@[stacks 059N "(2)"]
#check @CategoryTheory.ShortComplex.UniversallyExact.mittagLeffler_X₂

#check @Module.MittagLeffler.of_universallyInjective
#check @Module.MittagLeffler.of_exact
