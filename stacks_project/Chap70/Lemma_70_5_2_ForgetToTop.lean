module

public import Mathlib.Topology.Category.TopCat.Basic
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap70.Lemma_70_5_1_Points

/-!
# Underlying topological spaces of algebraic spaces

The forgetful functor sending an algebraic space over `S` to its space of
points, with the canonical topology of Lemma 66.4.6.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Identity morphisms of algebraic spaces act as the identity on underlying
topological spaces. -/
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

/-- The forgetful functor sending an algebraic space over `S` to its space of
points. -/
def forgetToTop {S : Scheme.{u}} : AlgebraicSpace S ⥤ TopCat.{u + 1} where
  obj X := TopCat.of (Points X)
  map f := TopCat.ofHom ⟨Points.map f, Points.continuous_map f⟩
  map_id := forgetToTop_map_id
  map_comp := forgetToTop_map_comp

/-- The object mapping of `forgetToTop` is the space of points. -/
theorem forgetToTop_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    forgetToTop.obj X = TopCat.of (Points X) :=
  sorry

/-- The action of `forgetToTop` on morphisms is the induced continuous map on
points. -/
theorem forgetToTop_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    forgetToTop.map f =
      TopCat.ofHom ⟨Points.map f, Points.continuous_map f⟩ :=
  sorry

/-- Forgetting the topology after `forgetToTop` recovers `pointsFunctor`. -/
theorem forgetToTop_comp_forget {S : Scheme.{u}} :
    (forgetToTop : AlgebraicSpace S ⥤ TopCat.{u + 1}) ⋙
        CategoryTheory.forget TopCat.{u + 1} =
      (pointsFunctor : AlgebraicSpace S ⥤ Type (u + 1)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
