/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map.Projection
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Comparison
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.NatTrans

/-!
# Functoriality of explicit pseudo-pullbacks

Aggregate for the action of cospan morphisms and `2`-cells on explicit pseudo-pullbacks. It
exports the map functor, its projection comparisons, identity and composition comparisons, and
the induced action on modifications. Import a leaf directly when only one layer is required.
-/
