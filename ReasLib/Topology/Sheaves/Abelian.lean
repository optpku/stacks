/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Abelian group valued (pre)sheaves

This module provides the standard Stacks-style notation for `AddCommGrpCat`-valued presheaves
and sheaves on a topological space, and re-exports the abelian category structure on sheaf
categories from `Mathlib.Topology.Sheaves.Abelian`.
-/

@[expose] public section

open TopCat

namespace TopCat

/-- The category of abelian-group-valued presheaves on a topological space. -/
scoped notation "PAb(" X ")" => Presheaf AddCommGrpCat X

/-- The category of abelian-group-valued sheaves on a topological space. -/
scoped notation "Ab(" X ")" => Sheaf AddCommGrpCat X

end TopCat
