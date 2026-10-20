/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Intrinsic
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex

/-!
# Cleavages and standard-fibre reindexing

Compatibility aggregate for the intrinsic cleavage owner and its derived standard-fibre
reindexing API. Focused consumers can import `Cleavage.Basic.Intrinsic` when they only need
chosen strongly cartesian lifts, or `Cleavage.Basic.Reindex` when they also need reindexing.
-/
