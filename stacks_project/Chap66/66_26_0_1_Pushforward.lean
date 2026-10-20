module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage

/-! # Compatibility view of module direct image on algebraic spaces

This module provides a compatibility view of the module direct-image construction and its
pullback adjunction.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → X.Modules ⥤ Y.Modules)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward_eq :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.Modules.pushforward f =
        (AlgebraicGeometry.AlgebraicSpace.ringedToposHom f).modulePushforward)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pullbackPushforwardAdjunction :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.Modules.pullback f ⊣
        AlgebraicGeometry.AlgebraicSpace.Modules.pushforward f)
