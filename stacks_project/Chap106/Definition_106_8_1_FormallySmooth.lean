module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormallySmooth
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap97.«97_6_0_1_Lifting»

/-!
# Formally smooth morphisms of algebraic stacks

A morphism of algebraic stacks is formally smooth when it is formally smooth
on objects as a 1-morphism of categories fibred in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.FormallySmooth :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.formallySmooth_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    FormallySmooth f ↔ Groupoids.Hom.FormallySmoothOnObjects f)

namespace FormallySmooth

#check (AlgebraicGeometry.AlgebraicStack.FormallySmooth.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    FormallySmooth (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.FormallySmooth.of_onObjects :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.FormallySmoothOnObjects f], FormallySmooth f)

#check (AlgebraicGeometry.AlgebraicStack.FormallySmooth.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [FormallySmooth f],
    Groupoids.Hom.FormallySmoothOnObjects f)

end FormallySmooth

end AlgebraicGeometry.AlgebraicStack
