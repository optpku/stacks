/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FiniteType

/-!
# Fibre dimension at specializations of generic points

This module relates the fibre dimension at a point to the fibre dimensions at the generic points
of the irreducible components containing it, giving both equality and upper-bound comparisons.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Let `f : X ⟶ Y` be locally of finite type and let `x : X`. If the stalk at `f x` is
Noetherian of Krull dimension at most one, and the fibre dimension is `d` at every generic point
of an irreducible component containing `x`, then the fibre dimension at `x` is `d`. -/
theorem fiberDimensionAt_eq_of_eq_at_genericPoints_specializingTo
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) (d : ℕ)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk (f x)))
    (hy_dim : ringKrullDim (Y.presheaf.stalk (f x)) ≤ 1)
    (hgeneric :
      ∀ η : X, η ∈ genericPoints X → Specializes η x →
        f.fiberDimensionAt η = d) :
    f.fiberDimensionAt x = d := sorry

namespace FiberDimension

/-- Let `f : X ⟶ Y` be locally of finite type and let `x : X`. Suppose that the stalk at `f x`
is Noetherian and that every generic point `η` of an irreducible component containing `x` has
`f η ≠ f x` and fibre dimension `d`. Then the fibre dimension at `x` is at most `d` plus the
Krull dimension of the base stalk minus one. -/
theorem at_le_generic_add_ringKrullDim_sub_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) (d : ℕ)
    (hy_noetherian : IsNoetherianRing (Y.presheaf.stalk (f x)))
    (hgeneric_image :
      ∀ η : X, η ∈ genericPoints X → Specializes η x → f η ≠ f x)
    (hgeneric_dim :
      ∀ η : X, η ∈ genericPoints X → Specializes η x →
        f.fiberDimensionAt η = d) :
    f.fiberDimensionAt x ≤
      (((d + (ringKrullDim (Y.presheaf.stalk (f x))).unbotD 0 - 1 : ℕ∞) : WithBot ℕ∞)) := sorry

end FiberDimension

end AlgebraicGeometry.Scheme.Hom
