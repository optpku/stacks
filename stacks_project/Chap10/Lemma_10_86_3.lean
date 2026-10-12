/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Sections

/-!
# Nonempty limits of countable Mittag-Leffler systems

@stack 0597

The result is canonically owned by the reusable sections API for countable Mittag-Leffler inverse
systems.
-/

@[expose] public section

/- Lemma 10.86.3 (Tag 0597): a countable Mittag-Leffler inverse system of nonempty sets has a
nonempty inverse limit. -/
@[stacks 0597]
#check @CategoryTheory.Functor.IsMittagLeffler.nonempty_sections_of_countable
