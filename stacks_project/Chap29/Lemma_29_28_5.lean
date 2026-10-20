/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.28.5: a finite type morphism to a quasi-compact scheme has uniformly bounded fibre
dimension. -/
@[stacks 0A3V]
#check (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_fiberDimensionAt_le :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.Scheme.Hom.FiniteType f] [CompactSpace Y],
    ∃ n : ℕ, ∀ x : X, f.fiberDimensionAt x ≤ (n : WithBot ℕ∞))
