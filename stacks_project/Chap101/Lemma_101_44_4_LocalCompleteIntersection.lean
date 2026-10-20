module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocalCompleteIntersection

/-!
# Local complete intersection morphisms of algebraic stacks

Typed compatibility checks for the shared local complete intersection API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.IsLocalCompleteIntersection :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.isLocalCompleteIntersection_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    IsLocalCompleteIntersection f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧
          AlgebraicSpace.IsLocalCompleteIntersection h)

#check (AlgebraicGeometry.AlgebraicStack.IsLocalCompleteIntersection.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    IsLocalCompleteIntersection (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.IsLocalCompleteIntersection.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsLocalCompleteIntersection f],
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.IsLocalCompleteIntersection h)

#check (AlgebraicGeometry.AlgebraicStack.IsLocalCompleteIntersection.of_toGroupoids :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.IsLocalCompleteIntersection f],
    IsLocalCompleteIntersection (AlgebraicSpace.toGroupoids.map f))

#check (AlgebraicGeometry.AlgebraicStack.IsLocalCompleteIntersection.of_comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [Smooth g] [IsLocalCompleteIntersection (f ≫ g)],
    IsLocalCompleteIntersection f)

end AlgebraicGeometry.AlgebraicStack
