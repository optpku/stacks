/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Equivalent formulations of the sheaf condition

Re-exports the four standard formulations of the sheaf condition for presheaves on topological
spaces, providing a single import for the full sheaf-condition API:

- `UniqueGluing`: unique amalgamation of compatible families
- `EqualizerProducts`: equalizer of product diagrams
- `PairwiseIntersections`: equalizer of pairwise-intersection products
- `Sites`: via the Grothendieck topology on opens
-/
