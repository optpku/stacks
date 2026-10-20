/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.Syntomic.AtPrime

@[expose] public section

/-!
# Syntomicity at a Prime Recall

The source equivalence is owned by pointwise predicates on an arbitrary
`RingHom`; the shared API separates its finite-presentation, flatness, and
complete-intersection-fiber components.

@stack 00SY
-/

/- Lemma 10.136.15, tag 00SY: for `q : Spec S`, syntomicity on a principal-open
neighbourhood of `q`, relative-global-complete-intersection on such a
neighbourhood, and the local finite-presentation/flat/local-fiber-complete-
intersection criterion are equivalent. -/
@[stacks 00SY "syntomicity at a prime"]
#check @RingHom.SyntomicAtPrime.iff_relativeGlobalCompleteIntersection

#check @RingHom.SyntomicAtPrime.iff_localCriterion

#check @RingHom.SyntomicAtPrime.tfae
