/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Proper

/-!
# Coherent pushforward along proper morphisms of algebraic spaces

Ordinary pushforward of a coherent module along a proper morphism to a
locally Noetherian algebraic space remains coherent, and is recorded as an
object of `Coh`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward_obj_isCoherent_of_proper :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] (F : X.Modules) [F.IsCoherent],
    ((Modules.pushforward f).obj F).IsCoherent)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.coherentPushforwardObj :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Proper f] (F : Coh X), Coh Y)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.coherentPushforwardObj_obj :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Proper f] (F : Coh X),
    (Modules.coherentPushforwardObj f F).obj = (Modules.pushforward f).obj F.obj)
