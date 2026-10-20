/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Tor
import StacksCheckRecall

@[expose] public section

/-!
# Symmetry of `Tor`

This source item is a recall of the reusable braided-monoidal `Tor` symmetry.  The canonical
owner is `CategoryTheory.torFlipIso` in ReasLib, so later chapters do not depend on Chap10 for
this homological infrastructure.

@stack 00M3
-/

-- Lemma 10.75.5, tag `00M3`: in a braided monoidal abelian category,
-- `(M, N) ↦ Tor_i(M, N)` is canonically isomorphic to `(M, N) ↦ Tor_i(N, M)`.
@[stacks 00M3]
#check @CategoryTheory.torFlipIso
