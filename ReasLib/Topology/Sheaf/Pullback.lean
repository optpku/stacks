/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Pullback.Composition
public import ReasLib.Topology.Sheaves.Pullback.Exactness
public import ReasLib.Topology.Sheaves.Pullback.FreeAbelianYoneda

/-!
# Sheaf pullback constructions

Canonical entry point for pullback (inverse image) sheaf constructions.
- Pullback composition coherence: `(f∘g)^{-1} ≅ g^{-1} ∘ f^{-1}`
- Exactness of inverse image for abelian sheaves
- Pullback comparison for sheafified free abelian Yoneda objects
-/
@[expose] public section

