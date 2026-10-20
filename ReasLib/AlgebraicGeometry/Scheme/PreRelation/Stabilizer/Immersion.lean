/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Stabilizer

/-!
# The stabilizer immersion of a pre-relation

The morphism from the stabilizer of a pre-relation to its arrow scheme is a locally closed
immersion.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The stabilizer of a pre-relation is a locally closed subscheme of its arrow scheme. -/
theorem isImmersion_stabilizerToArrows {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) :
    IsImmersion P.stabilizerToArrows.left := sorry

end AlgebraicGeometry.Scheme.PreRelation
