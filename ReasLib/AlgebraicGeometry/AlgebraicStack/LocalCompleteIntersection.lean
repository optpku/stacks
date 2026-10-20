module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth

/-!
# Local complete intersection morphisms of algebraic stacks

A morphism of algebraic stacks is a local complete intersection when some
smooth algebraic-space presentation square with surjective source atlas has
local-complete-intersection top arrow, in parallel with `AlgebraicStack.Flat`.
Local complete intersection morphisms cancel against smooth postcomposition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks over `S` is a local complete
intersection if some commutative square with algebraic-space vertices, smooth
vertical arrows, and surjective source atlas has local-complete-intersection
top arrow. -/
class IsLocalCompleteIntersection {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- There is a smooth presentation of `f` by algebraic spaces whose source
  atlas is surjective and whose top arrow is a local complete intersection. -/
  exists_surjective_smooth_presentation :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.IsLocalCompleteIntersection h

/-- A morphism of algebraic stacks is a local complete intersection if and only
if it admits a smooth algebraic-space presentation with surjective source atlas
and local-complete-intersection top arrow. -/
theorem isLocalCompleteIntersection_iff {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    IsLocalCompleteIntersection f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧
          AlgebraicSpace.IsLocalCompleteIntersection h := sorry

namespace IsLocalCompleteIntersection

/-- The identity morphism of an algebraic stack is a local complete
intersection. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    IsLocalCompleteIntersection (𝟙 X) := sorry

/-- A local complete intersection morphism of algebraic stacks admits a smooth
algebraic-space presentation with surjective source atlas and
local-complete-intersection top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsLocalCompleteIntersection f] :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.IsLocalCompleteIntersection h := sorry

/-- A local complete intersection morphism of algebraic spaces induces a
1-morphism of algebraic stacks that is a local complete intersection. -/
instance of_toGroupoids {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.IsLocalCompleteIntersection f] :
    IsLocalCompleteIntersection (AlgebraicSpace.toGroupoids.map f) := sorry

/-- If a composite morphism of algebraic stacks is a local complete intersection
and the second factor is smooth, then the first factor is a local complete
intersection. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [Smooth g] [IsLocalCompleteIntersection (f ≫ g)] :
    IsLocalCompleteIntersection f := sorry

end IsLocalCompleteIntersection

end AlgebraicGeometry.AlgebraicStack
