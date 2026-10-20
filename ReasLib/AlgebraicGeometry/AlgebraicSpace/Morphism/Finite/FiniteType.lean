/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Finite and integral morphisms locally of finite type

An integral morphism of algebraic spaces that is locally of finite type is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFinite

/-- An integral morphism of algebraic spaces that is locally of finite type is finite. -/
instance (priority := 900) of_isIntegralHom
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] [LocallyOfFiniteType f] : IsFinite f :=
  sorry

/-- A morphism of algebraic spaces that is locally of finite type is finite if and
only if it is integral. -/
theorem iff_isIntegralHom {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] : IsFinite f ↔ IsIntegralHom f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFinite
