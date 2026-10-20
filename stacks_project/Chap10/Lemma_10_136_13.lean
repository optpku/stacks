/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Syntomic

@[expose] public section

/-!
# Relative Global Complete-Intersection Syntomicity Recall

The source implication is an owner-level bridge between the intrinsic
relative-global-complete-intersection algebra predicate and syntomicity.

@stack 00SW
-/

/- Lemma 10.136.13, tag 00SW: every relative global complete-intersection
`R`-algebra is syntomic over `R`. -/
@[stacks 00SW "relative global complete intersections are syntomic"]
#check @Algebra.IsRelativeGlobalCompleteIntersection.syntomic
