/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Pullback of ample modules along embeddings

This file records preservation of ampleness for invertible scheme modules under
pullback along topological embeddings satisfying a quasi-compactness condition.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace IsAmple

/-- Pullback of an ample invertible module along an embedding is ample if either the morphism or
its source is quasi-compact. -/
theorem pullback_of_isEmbedding
    {X X' : Scheme.{u}} {L : X.Modules} [Invertible L] (hL : IsAmple L)
    (i : X' ⟶ X) (hi : IsEmbedding i) (hcompact : QuasiCompact i ∨ CompactSpace X') :
    IsAmple ((Scheme.Modules.pullback i).obj L) := sorry

end IsAmple

end AlgebraicGeometry.Scheme.Modules
