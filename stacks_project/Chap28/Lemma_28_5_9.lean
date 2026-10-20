/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Noetherian.ClosedPoints
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-!
# Lemma 28.5.9

The locally Noetherian scheme closed-point API is owned by
`ReasLib.AlgebraicGeometry.Noetherian.ClosedPoints`.
-/

/- Lemma 28.5.9 (1): any nonempty locally Noetherian scheme has a closed point. -/
@[stacks 02IL]
#check (AlgebraicGeometry.Scheme.exists_closedPoint :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [Nonempty X],
    Set.Nonempty (closedPoints X))

/- Lemma 28.5.9 (2): any nonempty closed subset of a locally Noetherian scheme has a closed
point. -/
@[stacks 02IL]
#check (AlgebraicGeometry.Scheme.exists_closedPoint_of_isClosed :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] {Z : Set X},
    IsClosed Z → Z.Nonempty → ∃ x : X, x ∈ Z ∧ x ∈ closedPoints X)

/- Lemma 28.5.9 (3): any point of a locally Noetherian scheme specializes to a closed point. -/
@[stacks 02IL]
#check (AlgebraicGeometry.Scheme.specializes_closedPoint :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X),
    ∃ y : X, x ⤳ y ∧ y ∈ closedPoints X)

end AlgebraicGeometry.Scheme
