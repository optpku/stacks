module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Points

/-!
# Points of directed affine inverse limits of algebraic spaces

The points functor and the comparison of points with directed affine inverse
limits are supplied by the shared algebraic-space API. These typed checks
preserve the public API for existing chapter imports.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (Cone IsLimit)
open CategoryTheory.Limits.Types (sectionOfCone)

universe u

#check (AlgebraicGeometry.AlgebraicSpace.pointsFunctor_map_id :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    TypeCat.ofHom (Points.map (𝟙 X)) = 𝟙 (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.pointsFunctor_map_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z),
    TypeCat.ofHom (Points.map (f ≫ g)) =
      TypeCat.ofHom (Points.map f) ≫ TypeCat.ofHom (Points.map g))

#check (AlgebraicGeometry.AlgebraicSpace.pointsFunctor :
    ∀ {S : Scheme.{u}}, AlgebraicSpace S ⥤ Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.pointsFunctor_obj :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    pointsFunctor.obj X = Points X)

#check (AlgebraicGeometry.AlgebraicSpace.pointsFunctor_map :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    pointsFunctor.map f = TypeCat.ofHom (Points.map f))

#check (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.sectionOfCone_apply :
    ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (x : Points c.pt)
    (i : OrderDual I),
    (sectionOfCone (pointsFunctor.mapCone c) x).val i =
      Points.map (c.π.app i) x)

#check (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.bijective_sectionOfCone :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c),
    Function.Bijective (sectionOfCone (pointsFunctor.mapCone c)))

#check (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.isLimit_pointsFunctor_mapCone :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c),
    Nonempty (IsLimit (pointsFunctor.mapCone c)))

#check (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.bijective_sectionOfCone_limit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)],
    Function.Bijective
      (sectionOfCone (pointsFunctor.mapCone (Limits.limit.cone D))))
