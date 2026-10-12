/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.ShortExact
import StacksCheckRecall

/-!
# Lemma 15.87.15

@stack 0CQB
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.87.15 (Stacks 0CQB): in a short exact sequence of sequential inverse systems, the
middle system is Mittag-Leffler when both outer systems are Mittag-Leffler.  This is a formal
property of sequential systems in any abelian category, owned by the neutral short-exact API. -/
@[stacks 0CQB]
#check @CategoryTheory.ShortComplex.ShortExact.MittagLeffler.middle_of_left_right

#check @CategoryTheory.SequentialInverseSystem.IsMittagLeffler
