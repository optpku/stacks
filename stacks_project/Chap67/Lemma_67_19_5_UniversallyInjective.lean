module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective

/-!
# Universally injective morphisms of algebraic spaces

A morphism of algebraic spaces is universally injective when every base change
induces an injective map on underlying point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.UniversallyInjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.universallyInjective_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    UniversallyInjective f ↔ universally pointsInjective f)

end AlgebraicGeometry.AlgebraicSpace
