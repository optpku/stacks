/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Composition
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Choice
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Identity
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Transport
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Coherence

@[expose] public section

/-!
# Cleavage reindexing comparison isomorphisms

Compatibility aggregate for canonical composition, identity, and change-of-cleavage comparisons,
equal-base-arrow transport, specified-composite comparisons, and their objectwise coherence API.
Focused consumers may import the corresponding leaf directly.
-/
