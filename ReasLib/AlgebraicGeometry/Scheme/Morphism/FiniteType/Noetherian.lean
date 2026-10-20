/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Noetherian schemes and finite type morphisms

This file records the global Noetherian consequence of a finite type scheme morphism.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The source of a finite type morphism to a Noetherian scheme is Noetherian. -/
theorem FiniteType.isNoetherian [FiniteType f] [IsNoetherian S] :
    IsNoetherian X := sorry

end AlgebraicGeometry.Scheme.Hom
