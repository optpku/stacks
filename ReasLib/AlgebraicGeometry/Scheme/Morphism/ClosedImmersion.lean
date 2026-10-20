/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Factorization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Factorization through closed immersions

For a reduced source, factorization through an arbitrary closed immersion is detected purely by
containment of the set-theoretic range. The canonical lift itself is owned by Mathlib's
`IsClosedImmersion.lift`; this file supplies the range-recognition API.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsClosedImmersion

/-- For a reduced source, kernel containment for a closed immersion is detected on ranges. -/
@[stacks 0356 "kernel containment and range recognition"]
theorem ker_le_ker_iff_range_subset
    {X Y Z : Scheme.{u}} [IsReduced Y]
    (i : Z ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X) :
    i.ker ≤ f.ker ↔ Set.range f ⊆ Set.range i := sorry

/-- Lemma 26.12.7 (1): a map from a reduced scheme factors through a closed immersion exactly when
its range lies in the range of that immersion. -/
@[stacks 0356 "factorization through a closed immersion"]
theorem exists_lift_iff_range_subset
    {X Y Z : Scheme.{u}} [IsReduced Y]
    (i : Z ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X) :
    (∃ g : Y ⟶ Z, g ≫ i = f) ↔ Set.range f ⊆ Set.range i := sorry

/-- The range criterion for factorization through a closed immersion, with uniqueness exposed. -/
@[stacks 0356 "unique factorization through a closed immersion"]
theorem existsUnique_lift_iff_range_subset
    {X Y Z : Scheme.{u}} [IsReduced Y]
    (i : Z ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X) :
    (∃! g : Y ⟶ Z, g ≫ i = f) ↔ Set.range f ⊆ Set.range i := sorry

end AlgebraicGeometry.IsClosedImmersion
