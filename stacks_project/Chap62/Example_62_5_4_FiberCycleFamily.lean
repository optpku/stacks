/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily

universe u

open AlgebraicGeometry

/- Compatibility bridge for existing consumers of the fibre-cycle family API. -/
#check (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily :
  {X S : Scheme.{u}} → (f : X ⟶ S) → [LocallyOfFiniteType f] → (k : ℤ) → Type u)
