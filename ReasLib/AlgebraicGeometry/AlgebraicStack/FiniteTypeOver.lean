module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Base

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is locally of finite type over a locally Noetherian scheme
`S` when it admits a surjective smooth atlas from a scheme locally of finite
type over `S`. -/
@[mk_iff]
class IsLocallyOfFiniteType {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop where
  /-- There is a surjective smooth 1-morphism from the slice of a scheme
  locally of finite type over `S`. -/
  exists_locallyOfFiniteType_smooth_cover :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.LocallyOfFiniteType U.hom

namespace IsLocallyOfFiniteType

/-- A locally of finite type algebraic stack admits a surjective smooth atlas
from a scheme locally of finite type over `S`. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsLocallyOfFiniteType X] :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.LocallyOfFiniteType U.hom :=
  IsLocallyOfFiniteType.exists_locallyOfFiniteType_smooth_cover

/-- A surjective smooth atlas from a scheme locally of finite type over `S`
witnesses that the algebraic stack is locally of finite type over `S`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [AlgebraicGeometry.LocallyOfFiniteType U.hom] :
    IsLocallyOfFiniteType X :=
  ⟨⟨U, p, inferInstance, inferInstance, inferInstance⟩⟩

/-- An algebraic stack is locally of finite type over `S` if and only if it
admits a surjective smooth atlas from a scheme locally of finite type over
`S`. -/
theorem iff {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsLocallyOfFiniteType X ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
          AlgebraicGeometry.LocallyOfFiniteType U.hom :=
  ⟨fun h => h.exists_locallyOfFiniteType_smooth_cover, fun h => ⟨h⟩⟩

end IsLocallyOfFiniteType

/-- The canonical slice of a scheme locally of finite type over `S` is a
locally of finite type algebraic stack. -/
instance instIsLocallyOfFiniteType_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.LocallyOfFiniteType U.hom] :
    IsLocallyOfFiniteType (GroupoidsOver.slice U) where
  exists_locallyOfFiniteType_smooth_cover :=
    ⟨U, 𝟙 (GroupoidsOver.slice U), inferInstance, inferInstance, inferInstance⟩

/-- Locally of finite type over `S` is equivalent to locally of finite type of
the structure morphism to the identity fibration of `Over S`. -/
theorem isLocallyOfFiniteType_iff_baseProjection {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsLocallyOfFiniteType X ↔
      LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X) := sorry

end AlgebraicGeometry.AlgebraicStack

