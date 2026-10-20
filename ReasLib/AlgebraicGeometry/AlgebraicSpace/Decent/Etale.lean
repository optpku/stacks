/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Decency under étale morphisms

The source of an étale morphism to a decent algebraic space is decent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsDecent

/-- The source of an étale morphism to a decent algebraic space is decent. -/
theorem of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Etale f] [IsDecent Y] : IsDecent X := sorry

end AlgebraicGeometry.AlgebraicSpace.IsDecent
