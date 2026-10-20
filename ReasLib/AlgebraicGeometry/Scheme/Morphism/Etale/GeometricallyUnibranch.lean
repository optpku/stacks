module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.RingTheory.Etale.Neighborhood.GeometricallyUnibranch

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom.UnramifiedAt

/-- A locally finite type morphism to an integral scheme is etale at a point
when the target is geometrically unibranch there, a generization maps to the
generic point, and the morphism is unramified at that point. -/
@[stacks 0GS8]
theorem etaleAt_of_specializes_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral Y] [LocallyOfFiniteType f] (x x' : X)
    (h_geom : Y.isGeometricallyUnibranchAt (f x)) (h_specializes : x' ⤳ x)
    (h_generic : f x' = genericPoint Y) (h_unramified : f.UnramifiedAt x) :
    f.EtaleAt x := sorry

end Scheme.Hom.UnramifiedAt

namespace Scheme.Hom.EtaleAt

/-- If a composite `f ≫ g` is étale at `x`, the integral scheme `Y` is geometrically
unibranch at `f x`, and a generalization of `x` maps to the generic point of `Y`, then
`f` is étale at `x`. -/
@[stacks 0GSA]
theorem left_of_comp_of_specializes_genericPoint {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral Y] (x x' : X)
    (h_geom : Y.isGeometricallyUnibranchAt (f x)) (h_specializes : x' ⤳ x)
    (h_generic : f x' = genericPoint Y) (h_comp : (f ≫ g).EtaleAt x) :
    f.EtaleAt x := sorry

/-- If a composite `f ≫ g` is étale at `x`, the integral scheme `Y` is geometrically
unibranch at `f x`, and a generalization of `x` maps to the generic point of `Y`, then
`g` is étale at `f x`. -/
@[stacks 0GSA]
theorem right_of_comp_of_specializes_genericPoint {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral Y] (x x' : X)
    (h_geom : Y.isGeometricallyUnibranchAt (f x)) (h_specializes : x' ⤳ x)
    (h_generic : f x' = genericPoint Y) (h_comp : (f ≫ g).EtaleAt x) :
    g.EtaleAt (f x) := sorry

/-- If `Y` is integral and geometrically unibranch, `f ≫ g` is étale, and every
irreducible component of `X` dominates `Y` through `f`, then `f` is étale. -/
@[stacks 0GSB]
theorem left_of_comp_of_dominantComponents {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral Y] [Etale (f ≫ g)]
    (h_geom : Y.isGeometricallyUnibranch)
    (h_components : ∀ C : irreducibleComponents X,
      IsDominant (X.irreducibleComponentSubschemeι C ≫ f)) :
    Etale f := sorry

/-- If `Y` is integral and geometrically unibranch, `f ≫ g` is étale, and every
irreducible component of `X` dominates `Y` through `f`, then `g` is étale at every
point in the image of `f`. -/
@[stacks 0GSB]
theorem right_of_comp_of_dominantComponents {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral Y] [Etale (f ≫ g)]
    (h_geom : Y.isGeometricallyUnibranch)
    (h_components : ∀ C : irreducibleComponents X,
      IsDominant (X.irreducibleComponentSubschemeι C ≫ f)) :
    ∀ x : X, g.EtaleAt (f x) := sorry

end Scheme.Hom.EtaleAt

namespace Scheme.Hom

/-- An unramified morphism from a connected scheme to an integral geometrically unibranch
scheme is étale if some irreducible component of the source dominates the target. -/
@[stacks 0GS9]
theorem etale_of_dominantComponent {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral Y] [ConnectedSpace X] [Unramified f]
    (h_geom : Y.isGeometricallyUnibranch)
    (h_component : ∃ Z : irreducibleComponents X,
      IsDominant (X.irreducibleComponentSubschemeι Z ≫ f)) :
    Etale f := sorry

/-- The connected source of an unramified morphism to an integral geometrically unibranch
scheme is irreducible if one of its irreducible components dominates the target. -/
@[stacks 0GS9]
theorem irreducibleSpace_of_dominantComponent {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral Y] [ConnectedSpace X] [Unramified f]
    (h_geom : Y.isGeometricallyUnibranch)
    (h_component : ∃ Z : irreducibleComponents X,
      IsDominant (X.irreducibleComponentSubschemeι Z ≫ f)) :
    IrreducibleSpace X := sorry

end Scheme.Hom

end AlgebraicGeometry
