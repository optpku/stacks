module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Submersive

/-!
# Submersive and universally submersive morphisms of algebraic spaces

A morphism of algebraic spaces is submersive when it induces a quotient map on
underlying point spaces, and universally submersive when every base change is
submersive. The canonical topology on `Points` is characterized rather than
constructed, so competing topologies remain explicit parameters.
-/

@[expose]
public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Submersive :
  {S : AlgebraicGeometry.Scheme.{u}} → {X Y : AlgebraicGeometry.AlgebraicSpace S} →
    (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.UniversallySubmersive :
  {S : AlgebraicGeometry.Scheme.{u}} → {X Y : AlgebraicGeometry.AlgebraicSpace S} →
    (X ⟶ Y) → Prop)
