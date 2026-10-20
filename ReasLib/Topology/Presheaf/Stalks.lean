/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Stalks.Filtered
public import ReasLib.Topology.Sheaves.Stalks.Pullback

/-!
# Presheaf stalks

Canonical entry point for stalk constructions on presheaves over topological spaces.
- `filteredStalkFunctor` — stalks as filtered colimits
- `stalkCompIso` — compatibility of stalks with colimit-preserving functors
- Stalk comparison for pullback presheaves
-/
