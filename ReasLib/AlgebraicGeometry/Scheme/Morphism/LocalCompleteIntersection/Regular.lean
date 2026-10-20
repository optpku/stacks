module

public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.Regular

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfFiniteType

/-- A morphism locally of finite type between regular schemes is a local complete intersection
morphism. -/
@[instance]
theorem isLocalCompleteIntersection_of_regular
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Scheme.Regular X] [Scheme.Regular Y] :
    LocallyOfType RingHom.IsLocalCompleteIntersection f := sorry

end AlgebraicGeometry.LocallyOfFiniteType

namespace AlgebraicGeometry.LocallyOfType

/-- In a commutative triangle of scheme morphisms over a locally Noetherian base, if the middle
scheme is regular, the second morphism is locally of finite type, and the composite is a local
complete intersection, then the first morphism is a local complete intersection. -/
@[stacks 0FJ2]
theorem isLocalCompleteIntersection_of_regular_of_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S)
    (hcomm : f ≫ g = h) [IsLocallyNoetherian S] [LocallyOfFiniteType g]
    [Scheme.Regular Y] (hX : LocallyOfType RingHom.IsLocalCompleteIntersection h) :
    LocallyOfType RingHom.IsLocalCompleteIntersection f := sorry

end AlgebraicGeometry.LocallyOfType

namespace AlgebraicGeometry.Scheme.Hom

/-- In a commutative triangle of scheme morphisms over a locally Noetherian base, if the middle
scheme is regular, the second morphism is locally of finite type, and the composite is a local
complete intersection, then the second morphism is Koszul at every image point of the first. -/
@[stacks 0FJ2]
theorem koszulAt_image_of_regular_of_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S)
    (hcomm : f ≫ g = h) [IsLocallyNoetherian S] [LocallyOfFiniteType g]
    [Scheme.Regular Y] (hX : LocallyOfType RingHom.IsLocalCompleteIntersection h) :
    ∀ x : X, g.KoszulAt (f x) := sorry

end AlgebraicGeometry.Scheme.Hom
