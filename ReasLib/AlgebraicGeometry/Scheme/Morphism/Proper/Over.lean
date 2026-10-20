module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over

/-!
# Proper morphisms in a slice category

This file records how properness of a scheme morphism is seen by the underlying-map
projection from a scheme slice category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A composite structure map packaged with `Over.mk` is proper when both factors are proper. -/
instance instIsProperOverMkComp
    {S X X' : Scheme.{u}} (p : X ⟶ S) (f : X' ⟶ X)
    [IsProper p] [IsProper f] :
    IsProper (Over.mk (f ≫ p) : Over S).hom := sorry

/-- An `Over S` morphism constructed from a proper scheme morphism is proper on its
underlying map. -/
instance instIsProperOverHomMk
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsProper i]
    {S : Scheme.{u}} {q : Y ⟶ S} :
    IsProper (Over.homMk i : Over.mk (i ≫ q) ⟶ Over.mk q).left := sorry

/-- The second projection of a pullback in `Over S` is proper when its first
projection is induced by a proper morphism. -/
instance instIsProperPullbackSnd
    {S : Scheme.{u}} {X Y Y' : Over S} (f : X ⟶ Y) [IsProper f.left]
    (i : Y' ⟶ Y) :
    IsProper (pullback.snd f i).left := sorry

/-- The source of the pullback of a proper morphism in `Over S` is locally of
finite type over `S` when the displayed objects are. -/
instance instLocallyOfFiniteTypePullbackSourceOfIsProper
    {S : Scheme.{u}} {X Y Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Y'.hom] (f : X ⟶ Y) [IsProper f.left] (i : Y' ⟶ Y) :
    LocallyOfFiniteType (pullback f i).hom := sorry

/-- The over-category morphism induced by the first map in a nested composite is proper
on underlying schemes when that first map is proper. -/
instance instIsProperNestedOverHomMk
    {S : Scheme.{u}} {X : Over S} {Z Z' : Scheme.{u}}
    (j : Z' ⟶ Z) (i : Z ⟶ X.left) [IsProper j] :
    IsProper
      (Over.homMk j (Category.assoc j i X.hom).symm :
        Over.mk ((j ≫ i) ≫ X.hom) ⟶ Over.mk (i ≫ X.hom)).left := sorry

end AlgebraicGeometry
