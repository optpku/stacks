/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap70.Lemma_70_18_1_FinitePresentationOver

/-!
# Base change of algebraic spaces of finite presentation

A morphism of schemes `g : S ⟶ S'` induces a functor on algebraic spaces by
restricting functors of points along `Over.map g`, and this preserves finite
presentation of the structure morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.ObjectProperty AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An isomorphism of functors of points induces an isomorphism of algebraic
spaces over the same base. -/
def isoOfFunctorOfPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (e : X.functorOfPoints ≅ Y.functorOfPoints) : X ≅ Y where
  hom := e.hom
  inv := e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The morphism `baseChange g X ⟶ baseChange g Y` obtained by whiskering a
morphism of algebraic spaces along `(Over.map g).op`. -/
def baseChangeMap {S S' : Scheme.{u}} (g : S ⟶ S') {X Y : AlgebraicSpace S'}
    (α : X ⟶ Y) : baseChange g X ⟶ baseChange g Y :=
  NatTrans.vcomp
    (NatTrans.vcomp (eqToHom (baseChange_functorOfPoints g X))
      (whiskerLeft (Over.map g).op α))
    (eqToHom (baseChange_functorOfPoints g Y).symm)

/-- Base change of algebraic spaces along a morphism of schemes, as a functor
on functors of points. -/
def baseChangeFunctor {S S' : Scheme.{u}} (g : S ⟶ S') :
    AlgebraicSpace S' ⥤ AlgebraicSpace S where
  obj X := baseChange g X
  map α := baseChangeMap g α
  map_id := sorry
  map_comp := sorry

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
      (eqToIso (baseChange_functorOfPoints (f ≫ g) X) ≪≫
        isoWhiskerRight (NatIso.op (Over.mapComp f g)).symm X.functorOfPoints ≪≫
        eqToIso (congrArg ((Over.map f).op ⋙ ·)
          (baseChange_functorOfPoints g X).symm) ≪≫
        eqToIso (baseChange_functorOfPoints f (baseChange g X)).symm))
    sorry

/-- Finite presentation over the base is stable under base change of the base
scheme. -/
instance baseChange_finitePresentation {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : AlgebraicSpace S') [FinitePresentation (toBase X)] :
    FinitePresentation (toBase (baseChange g X)) :=
  sorry

namespace FinitePresentationOver

/-- Base change along `g : S ⟶ S'` sends algebraic spaces of finite presentation
over `S'` to algebraic spaces of finite presentation over `S`. -/
theorem mapsTo {S S' : Scheme.{u}} (g : S ⟶ S') :
    finitePresentationOverProperty S' ≤
      (finitePresentationOverProperty S).inverseImage (baseChangeFunctor g) :=
  sorry

/-- Base change as a functor on categories of algebraic spaces of finite
presentation. -/
def baseChange {S S' : Scheme.{u}} (g : S ⟶ S') :
    FinitePresentationOver S' ⥤ FinitePresentationOver S :=
  FullSubcategory.restrict (baseChangeFunctor g) (mapsTo g)

/-- The underlying algebraic space of a restricted base change is the ambient
base change. -/
@[simp]
theorem baseChange_obj {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : FinitePresentationOver S') :
    ((baseChange g).obj X).obj = AlgebraicSpace.baseChange g X.obj :=
  sorry

/-- Restricted base change is transitive in the base morphism. -/
def compIso {S S' S'' : Scheme.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
    baseChange (f ≫ g) ≅ baseChange g ⋙ baseChange f :=
  NatIso.ofComponents
    (fun X ↦
      { hom := homMk ((baseChangeFunctor_comp f g).hom.app X.obj)
        inv := homMk ((baseChangeFunctor_comp f g).inv.app X.obj)
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

end FinitePresentationOver

end AlgebraicGeometry.AlgebraicSpace
