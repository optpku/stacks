/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.133.3

@stack 09CK

Lemma 10.133.3 (Tag 09CK): for a commutative `R`-algebra `S`,
`PrincipalParts.module R S M k` represents differential operators of order at most `k`.

The reusable quotient presentation and representing equivalence are owned by
`PrincipalParts`; this source file records the textbook label without creating
a chapter-local alias.
-/

@[stacks 09CK "principal-parts representation"]
#check @PrincipalParts.representingEquiv

#check @PrincipalParts.universalDifferential
#check @PrincipalParts.linearMap_ext
