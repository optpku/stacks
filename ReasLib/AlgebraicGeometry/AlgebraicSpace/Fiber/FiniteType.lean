/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.LocallyNoetherian

/-!
# Locally Noetherian fibres of locally finite type morphisms

A morphism of algebraic spaces that is locally of finite type has locally
Noetherian fibres.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.LocallyNoetherianFibers

/-- A morphism of algebraic spaces that is locally of finite type has locally
Noetherian fibres. -/
instance ofLocallyOfFiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] : LocallyNoetherianFibers f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallyNoetherianFibers
