module

public import Mathlib.Topology.Category.TopCat.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Functor

/-!
# The forgetful functor from algebraic spaces to topological spaces

Every algebraic space over a scheme has a space of points carrying its
canonical topology, and every morphism induces a continuous map on points.
These assignments form a functor, and forgetting the topology recovers the
functor of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Identity morphisms of algebraic spaces induce the identity continuous map
on underlying topological spaces. -/
theorem forgetToTop_map_id {S : Scheme.{u}} (X : AlgebraicSpace S) :
    TopCat.ofHom ⟨Points.map (𝟙 X), Points.continuous_map (𝟙 X)⟩ =
      𝟙 (TopCat.of (Points X)) :=
  sorry

/-- The induced maps on underlying topological spaces preserve composition of
morphisms of algebraic spaces. -/
theorem forgetToTop_map_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.ofHom ⟨Points.map (f ≫ g), Points.continuous_map (f ≫ g)⟩ =
      TopCat.ofHom ⟨Points.map f, Points.continuous_map f⟩ ≫
        TopCat.ofHom ⟨Points.map g, Points.continuous_map g⟩ :=
  sorry

/-- The forgetful functor sending an algebraic space over a scheme to its space
of points with its canonical topology. -/
def forgetToTop {S : Scheme.{u}} : AlgebraicSpace S ⥤ TopCat.{u + 1} where
  obj X := TopCat.of (Points X)
  map f := TopCat.ofHom ⟨Points.map f, Points.continuous_map f⟩
  map_id := forgetToTop_map_id
  map_comp := forgetToTop_map_comp

/-- The object mapping of the forgetful functor is the space of points. -/
theorem forgetToTop_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    forgetToTop.obj X = TopCat.of (Points X) :=
  rfl

/-- The action of the forgetful functor on morphisms is the induced continuous
map on points. -/
theorem forgetToTop_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    forgetToTop.map f =
      TopCat.ofHom ⟨Points.map f, Points.continuous_map f⟩ :=
  rfl

/-- Forgetting the topology after the forgetful functor recovers the functor of
points. -/
theorem forgetToTop_comp_forget {S : Scheme.{u}} :
    (forgetToTop : AlgebraicSpace S ⥤ TopCat.{u + 1}) ⋙
        CategoryTheory.forget TopCat.{u + 1} =
      (pointsFunctor : AlgebraicSpace S ⥤ Type (u + 1)) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
