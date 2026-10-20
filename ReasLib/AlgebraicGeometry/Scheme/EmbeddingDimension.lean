/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Embedding dimension of a scheme at a point

This module defines the intrinsic embedding dimension of a scheme at a point
from the cotangent space of its local ring.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The embedding dimension of a scheme at a point is the residue-field dimension of the
cotangent space of the local ring at that point. -/
@[stacks 0C2H]
noncomputable abbrev embeddingDimensionAt {X : Scheme.{u}} (x : X) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
    (IsLocalRing.CotangentSpace (X.presheaf.stalk x))

/-- The embedding dimension is computed by the residue-field finrank of the local cotangent
space. -/
@[stacks 0C2H]
theorem embeddingDimensionAt_eq_finrank_cotangentSpace {X : Scheme.{u}} (x : X) :
    embeddingDimensionAt x =
      Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) := sorry

/-- At a point of a locally Noetherian scheme, the embedding dimension is the minimal number of
generators of the maximal ideal of the local ring. -/
theorem embeddingDimensionAt_eq_spanFinrank {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X) :
    embeddingDimensionAt x =
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).spanFinrank := sorry

end

end AlgebraicGeometry.Scheme
