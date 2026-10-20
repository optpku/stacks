/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.IsEpi
import StacksCheckRecall

@[expose] public section

/-!
# Faithfully flat algebra epimorphisms

## Canonical recall

Stacks Lemma 10.107.7, tag `04VU`, is exactly
`Algebra.IsEpi.faithfullyFlat_bijective`. The reusable statement is owned by
ReasLib rather than duplicated as a chapter-local alias.

@stack 04VU
-/

@[stacks 04VU] #check @Algebra.IsEpi.faithfullyFlat_bijective
