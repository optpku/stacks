/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.FiniteSeparable
import StacksCheckRecall

/-!
# Finite separable extensions suffice for the existence part of the valuative criterion

For a morphism of algebraic spaces, the existence part of the valuative
criterion is equivalent to the same criterion restricted to dominating
extensions whose fraction-field extension is finite separable.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.41.3: The existence part of the valuative criterion is equivalent
to requiring finite separable fraction-field extensions. -/
@[stacks 03KH] #check
  (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence.iff_exists_finiteSeparable :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      ValuativeCriterion.Existence f ↔ ∀ sq : ValuativeCommSq f,
        ∃ e : sq.Extension, FiniteDimensional sq.K e.K' ∧ Algebra.IsSeparable sq.K e.K')
