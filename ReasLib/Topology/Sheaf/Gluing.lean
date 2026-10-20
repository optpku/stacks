/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.OpenCover.Gluing
public import ReasLib.Topology.Sheaves.OpenCover.Morphisms
public import ReasLib.Topology.Sheaves.OpenCover.Basis
public import ReasLib.Topology.Sheaves.OpenCover.Algebraic.Basis

/-!
# Gluing and descent for sheaves along open covers

Canonical entry point for the descent/gluing formalism on topological spaces.
- Descent data: `restrictToOpen`, `restrictToPair`, cocycle condition
- Gluing morphisms from an open cover
- Gluing on basis covers
- Algebraic realization of gluing data via `Gluing.BasisRealization`
-/
