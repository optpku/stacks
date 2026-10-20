/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedSequence.Properties
public import ReasLib.RingTheory.Normal.RationalSingularity
public import ReasLib.RingTheory.Normal.ReductionPossible

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace RationalSingularity.ReductionPossible

/-- A reduction-possible domain admits a finite normalized-blowup sequence with normal terminal
scheme and rational-singularity stalks at all closed points. -/
theorem exists_normalizedBlowupSequence
    (A : Type u) [CommRing A] [IsDomain A] [ReductionPossible A] :
    ∃ (X : Scheme.{u})
      (s : Scheme.NormalizedBlowupSequence (Spec (.of A)) X),
      X.isNormal ∧
        ∀ x : X, x ∈ closedPoints X →
          IsRationalSingularity (X.presheaf.stalk x) := sorry

end RationalSingularity.ReductionPossible
