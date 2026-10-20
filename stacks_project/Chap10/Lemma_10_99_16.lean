/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.RegularElement
import StacksCheckRecall

@[expose] public section

/-!
# Flatness across a regular element

Both clauses of Lemma 10.99.16 are the canonical regular-element criteria in
the `Module.Flat` and `Module.FaithfullyFlat` namespaces.

@stack 0H7N
-/

/- Lemma 10.99.16 (1): if `f` is regular on `A` and `M`, and the localization
away from `f` and the quotient by `f` are flat, then `M` is flat over `A`. -/
@[stacks 0H7N "(1), flat clause"]
#check @Module.Flat.of_regular_element

/- Lemma 10.99.16 (2): the same regular-element criterion holds with
`Module.Flat` replaced throughout by `Module.FaithfullyFlat`. -/
@[stacks 0H7N "(2), faithfully flat clause"]
#check @Module.FaithfullyFlat.of_regular_element
