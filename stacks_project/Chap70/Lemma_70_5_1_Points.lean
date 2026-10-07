module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap70.Lemma_70_4_1_Limit

/-!
# Points of directed affine inverse limits of algebraic spaces

The functor sending an algebraic space to its set of points, and the set-level
comparison of a directed inverse limit of decent algebraic spaces with affine
transitions against the inverse limit of the stagewise points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (Cone IsLimit)
open CategoryTheory.Limits.Types (sectionOfCone)

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

namespace AlgebraicGeometry.AlgebraicSpace.DirectedAffine

/-- The canonical comparison `sectionOfCone` of a points cone is stagewise
`Points.map` of the cone projections. -/
theorem sectionOfCone_apply {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (x : Points c.pt)
    (i : OrderDual I) :
    (sectionOfCone (pointsFunctor.mapCone c) x).val i =
      Points.map (c.π.app i) x :=
  sorry

/-- For a limiting cone of a directed inverse system of decent algebraic spaces
over `S` with affine transition morphisms, the canonical map from the points of
the limit to compatible families of stagewise points is bijective. -/
theorem bijective_sectionOfCone
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    Function.Bijective (sectionOfCone (pointsFunctor.mapCone c)) :=
  sorry

/-- A limiting cone of a directed affine system of decent algebraic spaces
remains limiting on points, up to existence of an `IsLimit` structure. -/
theorem isLimit_pointsFunctor_mapCone
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    Nonempty (IsLimit (pointsFunctor.mapCone c)) :=
  sorry

/-- The chosen directed affine inverse limit of decent algebraic spaces has
points equal to the inverse limit of the stagewise points, as sets. -/
theorem bijective_sectionOfCone_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)] :
    Function.Bijective
      (sectionOfCone (pointsFunctor.mapCone (Limits.limit.cone D))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
