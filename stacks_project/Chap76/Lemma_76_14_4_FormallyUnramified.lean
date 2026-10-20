module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified

/-!
# Formally unramified morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is formally unramified when it
is formally unramified as a transformation of functors of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.formallyUnramified_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      FormallyUnramified f ↔ Scheme.Over.FormallyUnramified f)

#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.of :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
      Scheme.Over.FormallyUnramified f → FormallyUnramified f)

#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.spec :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
      [FormallyUnramified f], Scheme.Over.FormallyUnramified f)

#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.id :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, FormallyUnramified (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.toSchemeOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
      [FormallyUnramified f], Scheme.Over.FormallyUnramified f)

end AlgebraicGeometry.AlgebraicSpace
