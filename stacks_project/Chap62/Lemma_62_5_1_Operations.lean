/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Hom

universe u

/- Fibrewise flat pullback remains available to source-side consumers. -/
#check (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.flatPullback :
  {X' X S : Scheme.{u}} → {f : X ⟶ S} → {f' : X' ⟶ S} →
    [LocallyOfFiniteType f] → [LocallyOfFiniteType f'] →
      (h : X' ⟶ X) → (hf : h ≫ f = f') → (e : ℕ) →
        [Flat h] → [RelativeDimension h e] → {r : ℤ} →
          (α : f.FiberCycleFamily r) → f'.FiberCycleFamily (r + (e : ℤ)))
