module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Additive
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Čech Hom-group maps of augmented simplicial algebraic spaces

Derived pullback along the augmentation gives restriction on Hom groups.
The two face pullbacks, conjugated by their canonical comparison isomorphisms,
define the Čech differential as their difference.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace CategoryTheory.Preadditive Functor
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}

/-- Each degree-one face followed by the degree-zero augmentation is the
degree-one augmentation. -/
theorem face_comp_augmentation (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (i : Fin 2) :
    U.δ i ≫ a.app (op ⦋0⦌) = a.app (op ⦋1⦌) := sorry

/-- The canonical identification of iterated face and augmentation pullback
with degree-one augmentation pullback. -/
def facePullbackIso (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (i : Fin 2) :
    modulePullbackDerived (a.app (op ⦋0⦌)) ⋙ modulePullbackDerived (U.δ i) ≅
      modulePullbackDerived (a.app (op ⦋1⦌)) :=
  modulePullbackDerived.compIso (U.δ i) (a.app (op ⦋0⦌)) ≪≫
    eqToIso (congrArg (fun h : U.obj (op ⦋1⦌) ⟶ X ↦ modulePullbackDerived h)
      (face_comp_augmentation a i))

/-- The face pullback identification is the composition comparison followed
by transport along the face-augmentation equality. -/
theorem facePullbackIso_eq (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (i : Fin 2) :
    facePullbackIso a i =
      modulePullbackDerived.compIso (U.δ i) (a.app (op ⦋0⦌)) ≪≫
        eqToIso (congrArg (fun h : U.obj (op ⦋1⦌) ⟶ X ↦ modulePullbackDerived h)
          (face_comp_augmentation a i)) := sorry

/-- The additive restriction map on Hom groups induced by degree-zero
augmentation pullback. -/
def homRestrict (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (K E : AlgebraicSpace.DerivedQCoh X) :
    AddCommGrpCat.of (K.obj ⟶ E.obj) ⟶
      AddCommGrpCat.of
        ((modulePullbackDerived (a.app (op ⦋0⦌))).obj K.obj ⟶
          (modulePullbackDerived (a.app (op ⦋0⦌))).obj E.obj) :=
  AddCommGrpCat.ofHom (modulePullbackDerived (a.app (op ⦋0⦌))).mapAddHom

/-- Restriction of a morphism is its derived pullback along the degree-zero
augmentation. -/
theorem homRestrict_apply (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (K E : AlgebraicSpace.DerivedQCoh X) (φ : K.obj ⟶ E.obj) :
    homRestrict a K E φ = (modulePullbackDerived (a.app (op ⦋0⦌))).map φ := sorry

/-- The additive face action on Hom groups, conjugated by the canonical
identifications with degree-one augmentation pullbacks. -/
def homDiffLeg (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (i : Fin 2) (K E : AlgebraicSpace.DerivedQCoh X) :
    AddCommGrpCat.of
        ((modulePullbackDerived (a.app (op ⦋0⦌))).obj K.obj ⟶
          (modulePullbackDerived (a.app (op ⦋0⦌))).obj E.obj) ⟶
      AddCommGrpCat.of
        ((modulePullbackDerived (a.app (op ⦋1⦌))).obj K.obj ⟶
          (modulePullbackDerived (a.app (op ⦋1⦌))).obj E.obj) :=
  AddCommGrpCat.ofHom
    ((leftComp _ ((facePullbackIso a i).app K.obj).inv).comp
      ((rightComp _ ((facePullbackIso a i).app E.obj).hom).comp
        (modulePullbackDerived (U.δ i)).mapAddHom))

/-- The face action sends a morphism to its face pullback conjugated by the
canonical pullback comparisons. -/
theorem homDiffLeg_apply (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (i : Fin 2) (K E : AlgebraicSpace.DerivedQCoh X)
    (φ : (modulePullbackDerived (a.app (op ⦋0⦌))).obj K.obj ⟶
      (modulePullbackDerived (a.app (op ⦋0⦌))).obj E.obj) :
    homDiffLeg a i K E φ =
      ((facePullbackIso a i).app K.obj).inv ≫
        (modulePullbackDerived (U.δ i)).map φ ≫
          ((facePullbackIso a i).app E.obj).hom := sorry

/-- The Čech Hom differential from degree zero to degree one is the difference
of the zeroth and first conjugated face actions. -/
def homDiff (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (K E : AlgebraicSpace.DerivedQCoh X) :
    AddCommGrpCat.of
        ((modulePullbackDerived (a.app (op ⦋0⦌))).obj K.obj ⟶
          (modulePullbackDerived (a.app (op ⦋0⦌))).obj E.obj) ⟶
      AddCommGrpCat.of
        ((modulePullbackDerived (a.app (op ⦋1⦌))).obj K.obj ⟶
          (modulePullbackDerived (a.app (op ⦋1⦌))).obj E.obj) :=
  homDiffLeg a 0 K E - homDiffLeg a 1 K E

/-- The Čech differential evaluates as the difference of its two face actions. -/
theorem homDiff_apply (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (K E : AlgebraicSpace.DerivedQCoh X)
    (φ : (modulePullbackDerived (a.app (op ⦋0⦌))).obj K.obj ⟶
      (modulePullbackDerived (a.app (op ⦋0⦌))).obj E.obj) :
    homDiff a K E φ = homDiffLeg a 0 K E φ - homDiffLeg a 1 K E φ := sorry

/-- Restriction followed by the Čech Hom differential is zero. -/
theorem homRestrict_comp_homDiff (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (K E : AlgebraicSpace.DerivedQCoh X) :
    homRestrict a K E ≫ homDiff a K E = 0 := sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
