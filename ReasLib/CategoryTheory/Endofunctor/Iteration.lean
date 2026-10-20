/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Endofunctor.Iteration.Center
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Cosimplicial
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Simplicial

/-!
# Iterated endofunctors

Compatibility facade for the reusable iteration API. Downstream files should import the
narrowest of `Core`, `Positive`, `Center`, `Cosimplicial`, and `Simplicial`.
-/
