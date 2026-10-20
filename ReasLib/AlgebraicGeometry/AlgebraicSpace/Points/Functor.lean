module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# The functor of points of algebraic spaces as sets

Algebraic spaces and their morphisms determine sets of points and maps of sets.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Identity morphisms of algebraic spaces act as the identity on points. -/
theorem pointsFunctor_map_id {S : Scheme.{u}} (X : AlgebraicSpace S) :
    TypeCat.ofHom (Points.map (𝟙 X)) = 𝟙 (Points X) :=
  sorry

/-- The induced maps on points preserve composition of morphisms of algebraic
spaces. -/
theorem pointsFunctor_map_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    TypeCat.ofHom (Points.map (f ≫ g)) =
      TypeCat.ofHom (Points.map f) ≫ TypeCat.ofHom (Points.map g) :=
  sorry

/-- The functor sending an algebraic space over `S` to its set of points. -/
def pointsFunctor {S : Scheme.{u}} : AlgebraicSpace S ⥤ Type (u + 1) where
  obj X := Points X
  map f := TypeCat.ofHom (Points.map f)
  map_id := pointsFunctor_map_id
  map_comp := pointsFunctor_map_comp

/-- The object mapping of `pointsFunctor` is the set of points. -/
theorem pointsFunctor_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    pointsFunctor.obj X = Points X :=
  sorry

/-- The action of `pointsFunctor` on morphisms is the induced map on points. -/
theorem pointsFunctor_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    pointsFunctor.map f = TypeCat.ofHom (Points.map f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
