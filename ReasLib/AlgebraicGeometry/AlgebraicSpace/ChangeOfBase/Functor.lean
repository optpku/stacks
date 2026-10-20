module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import Mathlib.CategoryTheory.Whiskering

/-!
# Functorial base change of algebraic spaces

Base change acts on morphisms by restriction of natural transformations and
commutes with composition of base morphisms up to a canonical isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An isomorphism of functors of points induces an isomorphism of algebraic
spaces over the same base. -/
def isoOfFunctorOfPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (e : X.functorOfPoints ≅ Y.functorOfPoints) : X ≅ Y where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- The morphism `baseChange g X ⟶ baseChange g Y` obtained by whiskering a
morphism of algebraic spaces along `(Over.map g).op`. -/
def baseChangeMap {S S' : Scheme.{u}} (g : S ⟶ S') {X Y : AlgebraicSpace S'}
    (α : X ⟶ Y) : baseChange g X ⟶ baseChange g Y :=
  whiskerLeft (Over.map g).op α

/-- Base change of algebraic spaces along a morphism of schemes, as a functor
on functors of points. -/
def baseChangeFunctor {S S' : Scheme.{u}} (g : S ⟶ S') :
    AlgebraicSpace S' ⥤ AlgebraicSpace S where
  obj X := baseChange g X
  map α := baseChangeMap g α
  map_id := fun _ ↦ rfl
  map_comp := fun _ _ ↦ rfl

/-- The object map of `baseChangeFunctor g` is `baseChange g`. -/
@[simp]
theorem baseChangeFunctor_obj {S S' : Scheme.{u}} (g : S ⟶ S') (X : AlgebraicSpace S') :
    (baseChangeFunctor g).obj X = baseChange g X :=
  rfl

/-- The morphism map of `baseChangeFunctor g` is `baseChangeMap g`. -/
@[simp]
theorem baseChangeFunctor_map {S S' : Scheme.{u}} (g : S ⟶ S')
    {X Y : AlgebraicSpace S'} (α : X ⟶ Y) :
    (baseChangeFunctor g).map α = baseChangeMap g α :=
  rfl

/-- Base change of algebraic spaces is transitive in the base morphism. -/
def baseChangeFunctor_comp {S S' S'' : Scheme.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
    baseChangeFunctor (f ≫ g) ≅ baseChangeFunctor g ⋙ baseChangeFunctor f :=
  NatIso.ofComponents
    (fun X ↦ isoOfFunctorOfPoints
      (eqToIso (rfl : (AlgebraicSpace.baseChange (f ≫ g) X).functorOfPoints =
          (Over.map (f ≫ g)).op ⋙ X.functorOfPoints) ≪≫
        isoWhiskerRight (NatIso.op (Over.mapComp f g)).symm X.functorOfPoints ≪≫
        eqToIso (rfl : (Over.map f).op ⋙ (Over.map g).op ⋙ X.functorOfPoints =
          (Over.map f).op ⋙ (AlgebraicSpace.baseChange g X).functorOfPoints) ≪≫
        eqToIso (rfl : (Over.map f).op ⋙ (AlgebraicSpace.baseChange g X).functorOfPoints =
          (AlgebraicSpace.baseChange f (AlgebraicSpace.baseChange g X)).functorOfPoints)))
    sorry

end AlgebraicGeometry.AlgebraicSpace
