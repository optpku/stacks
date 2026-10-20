module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
import StacksCheckRecall

/-!
# Surjective morphisms of algebraic spaces

Definition 67.5.2 (03ME) says that a morphism is surjective when its map on
associated points is surjective. The canonical property and its API are owned
by `ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

@[stacks 03ME] #check (Surjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

@[stacks 03ME] #check (surjective_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Surjective f ↔ Function.Surjective (Points.map f))

end AlgebraicGeometry.AlgebraicSpace
