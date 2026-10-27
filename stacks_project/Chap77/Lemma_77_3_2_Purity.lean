/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity

/-!
# Purity of modules on algebraic spaces

Purity and universal purity above points, and their relative versions, are
provided by the shared module-purity API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsPureAlong :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType], Points Y → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsUniversallyPureAlong :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType], Points Y → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsPureOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType], Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsUniversallyPureOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType], Prop)

end AlgebraicGeometry.AlgebraicSpace.Modules
