/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.InvariantMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.InvariantBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Functoriality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets.Functoriality
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Associator
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Postcomposition
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Base change of quotient stacks

The quotient of an invariant base change forms the canonical two-cartesian square
with the original quotient and the stacks of points of the two base spaces.
-/

@[expose] public section

-- Exposed square data reference private comparison constructions and their laws.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The cartesian `1`-morphism `[U/R] ⟶ 𝒮_B` after aligning Hom-universes. -/
def toSpaceHomCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (fppfQuotientStack G).p (stackInSetsULift B).p :=
  (toBase G).comp (stackInSetsULift.up B)

/-- The `1`-morphism `[U/R] ⟶ 𝒮_B` of stacks in groupoids over `(Sch/S)_fppf`. -/
def toSpaceHom {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    fppfQuotientStack G ⟶ stackInSetsULift B :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (toSpaceHomCartesian G).toBasedFunctor)

/-- `toSpaceHom G` is the universe-aligned lift of the quotient structure morphism. -/
theorem toSpaceHom_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    StackOver.Groupoids.Hom.toCartesianBasedFunctor (toSpaceHom G) =
      toSpaceHomCartesian G := sorry

/-- The cartesian top arrow `[U'/R'] ⟶ [U/R]` induced by the base-change projection. -/
def baseChangeQuotientMapCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    CartesianBasedFunctor (fppfQuotientStack (changeBase g.left (baseChange g.left (over G φ hφ)))).p
      (fppfQuotientStack (over G φ hφ)).p :=
  Hom.quotientStackMap (baseChangeProjection g.left (over G φ hφ))

/-- The top arrow `[U'/R'] ⟶ [U/R]` as a morphism of stacks in groupoids. -/
def baseChangeQuotientMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    fppfQuotientStack (changeBase g.left (baseChange g.left (over G φ hφ))) ⟶
      fppfQuotientStack (over G φ hφ) :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor
      (baseChangeQuotientMapCartesian G φ hφ g).toBasedFunctor)

/-- The structure morphism to the new base is invariant under the transported
base-changed groupoid. -/
private theorem baseChangeToSpace_invariant {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (changeBase g.left (baseChange g.left (over G φ hφ))).s.left ≫ (baseChange g.left (over G φ hφ)).U.hom =
      (changeBase g.left (baseChange g.left (over G φ hφ))).t.left ≫ (baseChange g.left (over G φ hφ)).U.hom
        := sorry

/-- The cartesian left arrow `[U'/R'] ⟶ 𝒮_{X'}` induced by the structure morphism of `U'`
over `X'`, on the transported quotient stack. -/
def baseChangeToSpaceHomCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    CartesianBasedFunctor (fppfQuotientStack (changeBase g.left (baseChange g.left (over G φ hφ)))).p
      (stackInSetsULift X'.left).p :=
  (fppfToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ hφ)).U.hom
    (baseChangeToSpace_invariant G φ hφ g)).comp
    (stackInSetsULift.up X'.left)

/-- The left arrow `[U'/R'] ⟶ 𝒮_{X'}` as a morphism of stacks in groupoids. -/
def baseChangeToSpaceHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    fppfQuotientStack (changeBase g.left (baseChange g.left (over G φ hφ))) ⟶ stackInSetsULift X'.left :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor
      (baseChangeToSpaceHomCartesian G φ hφ g).toBasedFunctor)

/-- The prestack projection followed by the structure morphism agrees objectwise
with the transported structure morphism. -/
private theorem baseChangePrestackMap_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X)
    (x : (preQuotient (changeBase g.left (baseChange g.left (over G φ hφ)))).total) :
    ((Hom.prestackMap (baseChangeProjection g.left (over G φ hφ))).comp (preQuotientToBase (over G φ
      hφ))).toFunctor.obj x = (preQuotientToBase (changeBase g.left (baseChange g.left (over G φ
      hφ)))).toFunctor.obj x := sorry

/-- Equality transport between the two prestack composites is natural. -/
private theorem baseChangePrestackMapIso_naturality {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    let F := (Hom.prestackMap (baseChangeProjection g.left (over G φ hφ))).comp (preQuotientToBase (over G φ
      hφ))
    let H := (preQuotientToBase (changeBase g.left (baseChange g.left (over G φ hφ))))
    ∀ {x y : (preQuotient (changeBase g.left (baseChange g.left (over G φ hφ)))).total} (f : x ⟶ y),
      F.toFunctor.map f ≫ (eqToIso (baseChangePrestackMap_obj G φ hφ g y)).hom =
        (eqToIso (baseChangePrestackMap_obj G φ hφ g x)).hom ≫ H.toFunctor.map f := sorry

/-- Equality transport between the two prestack composites lies over an identity. -/
private theorem baseChangePrestackMapIso_isHomLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X)
    (x : (preQuotient (changeBase g.left (baseChange g.left (over G φ hφ)))).total) :
    (stackInSets X.left).p.IsHomLift
      (𝟙 ((preQuotient (changeBase g.left (baseChange g.left (over G φ hφ)))).p.obj x)) (eqToIso
        (baseChangePrestackMap_obj G φ hφ g x)).hom := sorry

/-- The two prestack composites are canonically isomorphic over the scheme base. -/
private def baseChangePrestackMapIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    ((Hom.prestackMap (baseChangeProjection g.left (over G φ hφ))).comp (preQuotientToBase (over G φ hφ))) ≅
      (preQuotientToBase (changeBase g.left (baseChange g.left (over G φ hφ)))) :=
  ObjectProperty.isoMk _ (BasedNatIso.ofComponents
    (F := ((Hom.prestackMap (baseChangeProjection g.left (over G φ hφ))).comp (preQuotientToBase (over G φ
      hφ))).toBasedFunctor)
    (G := (preQuotientToBase (changeBase g.left (baseChange g.left (over G φ hφ)))).toBasedFunctor)
    (fun x ↦ eqToIso (baseChangePrestackMap_obj G φ hφ g x))
    (baseChangePrestackMapIso_naturality G φ hφ g)
    (baseChangePrestackMapIso_isHomLift G φ hφ g))

/-- The invariant map to the new base followed by the base-change map agrees
objectwise with the transported structure morphism. -/
private theorem baseChangePrestackSpaceMap_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X)
    (x : (preQuotient (changeBase g.left (baseChange g.left (over G φ hφ)))).total) :
    ((prestackToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ
      hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g)).comp (stackInSets.map g.left)).toFunctor.obj x =
      (preQuotientToBase (changeBase g.left (baseChange g.left (over G φ hφ)))).toFunctor.obj x := sorry

/-- Equality transport between the two prestack composites is natural. -/
private theorem baseChangePrestackSpaceMapIso_naturality {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    let F := (prestackToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G
      φ hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g)).comp (stackInSets.map g.left)
    let H := (preQuotientToBase (changeBase g.left (baseChange g.left (over G φ hφ))))
    ∀ {x y : (preQuotient (changeBase g.left (baseChange g.left (over G φ hφ)))).total} (f : x ⟶ y),
      F.toFunctor.map f ≫ (eqToIso (baseChangePrestackSpaceMap_obj G φ hφ g y)).hom =
        (eqToIso (baseChangePrestackSpaceMap_obj G φ hφ g x)).hom ≫ H.toFunctor.map f := sorry

/-- Equality transport between the two prestack composites lies over an identity. -/
private theorem baseChangePrestackSpaceMapIso_isHomLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X)
    (x : (preQuotient (changeBase g.left (baseChange g.left (over G φ hφ)))).total) :
    (stackInSets X.left).p.IsHomLift
      (𝟙 ((preQuotient (changeBase g.left (baseChange g.left (over G φ hφ)))).p.obj x)) (eqToIso
        (baseChangePrestackSpaceMap_obj G φ hφ g x)).hom := sorry

/-- The two prestack composites are canonically isomorphic over the scheme base. -/
private def baseChangePrestackSpaceMapIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    ((prestackToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ
      hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g)).comp (stackInSets.map g.left)) ≅ (preQuotientToBase
      (changeBase g.left (baseChange g.left (over G φ hφ)))) :=
  ObjectProperty.isoMk _ (BasedNatIso.ofComponents
    (F := ((prestackToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ
      hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g)).comp (stackInSets.map g.left)).toBasedFunctor)
    (G := (preQuotientToBase (changeBase g.left (baseChange g.left (over G φ hφ)))).toBasedFunctor)
    (fun x ↦ eqToIso (baseChangePrestackSpaceMap_obj G φ hφ g x))
    (baseChangePrestackSpaceMapIso_naturality G φ hφ g)
    (baseChangePrestackSpaceMapIso_isHomLift G φ hφ g))

/-- The quotient projection followed by the structure map is a lift of the
transported prestack structure morphism. -/
private def baseChangeQuotientLeftLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation (changeBase g.left (baseChange g.left (over G φ hφ)))).comparison)
        (preQuotientToBase (changeBase g.left (baseChange g.left (over G φ hφ)))) where
  lift := (Hom.quotientStackMap (baseChangeProjection g.left (over G φ hφ))).comp (toBase (over G φ hφ))
  comparison :=
    (CartesianBasedFunctor.associator
      (fppfQuotientStackPresentation (changeBase g.left (baseChange g.left (over G φ hφ)))).comparison
      (Hom.quotientStackMap (baseChangeProjection g.left (over G φ hφ))) (toBase (over G φ hφ))).symm ≪≫
    (CartesianBasedFunctor.postcomp (preQuotient (changeBase g.left (baseChange g.left (over G φ hφ)))).p
      (toBase (over G φ hφ))).mapIso
      (Hom.quotientStackMap_comp (baseChangeProjection g.left (over G φ hφ))) ≪≫
    CartesianBasedFunctor.associator (Hom.prestackMap (baseChangeProjection g.left (over G φ hφ)))
      (fppfQuotientStackPresentation (over G φ hφ)).comparison (toBase (over G φ hφ)) ≪≫
    (CartesianBasedFunctor.precomp (stackInSets X.left).p
      (Hom.prestackMap (baseChangeProjection g.left (over G φ hφ)))).mapIso (toBase_comp (over G φ hφ)) ≪≫
    baseChangePrestackMapIso G φ hφ g

/-- The invariant quotient morphism followed by the base-change map is a lift of
the transported prestack structure morphism. -/
private def baseChangeQuotientRightLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation (changeBase g.left (baseChange g.left (over G φ hφ)))).comparison)
        (preQuotientToBase (changeBase g.left (baseChange g.left (over G φ hφ)))) where
  lift := (fppfToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ
    hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g)).comp (stackInSets.map g.left)
  comparison :=
    (CartesianBasedFunctor.associator
      (fppfQuotientStackPresentation (changeBase g.left (baseChange g.left (over G φ hφ)))).comparison
        (fppfToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ
        hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g))
      (stackInSets.map g.left)).symm ≪≫
    (CartesianBasedFunctor.postcomp (preQuotient (changeBase g.left (baseChange g.left (over G φ hφ)))).p
      (stackInSets.map g.left)).mapIso
      (fppfToSpace_comp (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ
        hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g)) ≪≫
    baseChangePrestackSpaceMapIso G φ hφ g

/-- The two quotient morphisms to the original base are canonically isomorphic. -/
private def baseChangeQuotientUnliftedIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (Hom.quotientStackMap (baseChangeProjection g.left (over G φ hφ))).comp (toBase (over G φ hφ)) ≅
      (fppfToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ
        hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g)).comp (stackInSets.map g.left) :=
  CartesianBasedFunctor.IsStackification.LiftChoice.comparisonIso
    (fppfQuotientStackPresentation (changeBase g.left (baseChange g.left (over G φ hφ)))).isStackification
    (baseChangeQuotientLeftLift G φ hφ g) (baseChangeQuotientRightLift G φ hφ g)

/-- The components of the universe-alignment comparison are natural. -/
private theorem baseChangeQuotientIsoRightAlign_naturality {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    let F := ((fppfToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ
      hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g)).comp (stackInSets.map g.left)).comp
      (stackInSetsULift.up X.left)
    let H := (baseChangeToSpaceHomCartesian G φ hφ g).comp (StackOver.Groupoids.Hom.toCartesianBasedFunctor
      (stackInSetsULift.map g.left))
    let e := fun x ↦ ((stackInSets.map g.left).comp (stackInSetsULift.up X.left)).toFunctor.mapIso
        ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
          (stackInSets X'.left).total).unitIso.app
          ((fppfToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ
            hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g)).toFunctor.obj x))
    ∀ {x y : (fppfQuotientStack (changeBase g.left (baseChange g.left (over G φ hφ)))).total} (f : x ⟶ y),
      F.toFunctor.map f ≫ (e y).hom = (e x).hom ≫ H.toFunctor.map f := sorry

/-- The universe-alignment comparison lies over the identity of each base scheme. -/
private theorem baseChangeQuotientIsoRightAlign_isHomLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X)
    (x : (fppfQuotientStack (changeBase g.left (baseChange g.left (over G φ hφ)))).total) :
    (stackInSetsULift X.left).p.IsHomLift
      (𝟙 ((fppfQuotientStack (changeBase g.left (baseChange g.left (over G φ hφ)))).p.obj x))
      (((stackInSets.map g.left).comp (stackInSetsULift.up X.left)).toFunctor.mapIso
        ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
          (stackInSets X'.left).total).unitIso.app
          ((fppfToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ
            hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g)).toFunctor.obj x))).hom := sorry

/-- The unit of the two-universe equivalence aligns the two quotient composites. -/
private def baseChangeQuotientIsoRightAlign {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    ((fppfToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ
      hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g)).comp (stackInSets.map g.left)).comp
      (stackInSetsULift.up X.left) ≅ (baseChangeToSpaceHomCartesian G φ hφ g).comp
      (StackOver.Groupoids.Hom.toCartesianBasedFunctor (stackInSetsULift.map g.left)) :=
  ObjectProperty.isoMk _ (BasedNatIso.ofComponents
    (F := (((fppfToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ
      hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g)).comp (stackInSets.map g.left)).comp
      (stackInSetsULift.up X.left)).toBasedFunctor)
    (G := ((baseChangeToSpaceHomCartesian G φ hφ g).comp (StackOver.Groupoids.Hom.toCartesianBasedFunctor
      (stackInSetsULift.map g.left))).toBasedFunctor)
    (fun x ↦ ((stackInSets.map g.left).comp (stackInSetsULift.up X.left)).toFunctor.mapIso
        ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
          (stackInSets X'.left).total).unitIso.app
          ((fppfToSpace (changeBase g.left (baseChange g.left (over G φ hφ))) (baseChange g.left (over G φ
            hφ)).U.hom (baseChangeToSpace_invariant G φ hφ g)).toFunctor.obj x)))
    (baseChangeQuotientIsoRightAlign_naturality G φ hφ g)
    (baseChangeQuotientIsoRightAlign_isHomLift G φ hφ g))

/-- The cartesian `2`-isomorphism of the two composites `[U'/R'] ⟶ 𝒮_X`. -/
private def baseChangeQuotientIsoCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeQuotientMapCartesian G φ hφ g).comp
        (toSpaceHomCartesian (over G φ hφ)) ≅
      (baseChangeToSpaceHomCartesian G φ hφ g).comp (StackOver.Groupoids.Hom.toCartesianBasedFunctor
        (stackInSetsULift.map g.left)) :=
  (CartesianBasedFunctor.associator (Hom.quotientStackMap (baseChangeProjection g.left (over G φ hφ)))
    (toBase (over G φ hφ)) (stackInSetsULift.up X.left)).symm ≪≫
    (CartesianBasedFunctor.postcomp
        (fppfQuotientStack (changeBase g.left (baseChange g.left (over G φ hφ)))).p
        (stackInSetsULift.up X.left)).mapIso
      (baseChangeQuotientUnliftedIso G φ hφ g) ≪≫
    baseChangeQuotientIsoRightAlign G φ hφ g

/-- The invertible `2`-cell of the quotient base-change square, oriented `fst ≫ right ≅ snd ≫ bottom`. -/
def baseChangeQuotientIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    baseChangeQuotientMap G φ hφ g ≫ toSpaceHom (over G φ hφ) ≅
      baseChangeToSpaceHom G φ hφ g ≫ stackInSetsULift.map g.left :=
  StackOver.Groupoids.Hom.isoMk
    (FiberedCategoryOver.Groupoids.BasedFunctorIso.lift
      (CartesianBasedFunctor.toBasedIso (baseChangeQuotientIsoCartesian G φ hφ g)))

/-- The `2`-commutative square with apex `[U'/R']`, top arrow `[U'/R'] ⟶ [U/R]`,
left arrow `[U'/R'] ⟶ 𝒮_{X'}`, and bottom arrow `𝒮_{X'} ⟶ 𝒮_X`. -/
def baseChangeQuotientCone {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    PseudoPullbackCone (toSpaceHom (over G φ hφ)) (stackInSetsULift.map g.left) where
  pt := fppfQuotientStack (changeBase g.left (baseChange g.left (over G φ hφ)))
  fst := baseChangeQuotientMap G φ hφ g
  snd := baseChangeToSpaceHom G φ hφ g
  iso := baseChangeQuotientIso G φ hφ g

/-- The apex of `baseChangeQuotientCone` is `[U'/R']`. -/
theorem baseChangeQuotientCone_pt {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeQuotientCone G φ hφ g).pt =
      fppfQuotientStack (changeBase g.left (baseChange g.left (over G φ hφ))) := rfl

/-- The first projection of `baseChangeQuotientCone` is `[U'/R'] ⟶ [U/R]`. -/
theorem baseChangeQuotientCone_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeQuotientCone G φ hφ g).fst = baseChangeQuotientMap G φ hφ g := rfl

/-- The second projection of `baseChangeQuotientCone` is `[U'/R'] ⟶ 𝒮_{X'}`. -/
theorem baseChangeQuotientCone_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeQuotientCone G φ hφ g).snd = baseChangeToSpaceHom G φ hφ g := rfl

/-- The `2`-cell of `baseChangeQuotientCone` is `baseChangeQuotientIso`. -/
theorem baseChangeQuotientCone_iso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeQuotientCone G φ hφ g).iso = baseChangeQuotientIso G φ hφ g := rfl

/-- Quotient-stack formation commutes with invariant base change: the canonical
square over the stacks of points is a bicategorical pullback. -/
theorem baseChangeQuotientCone_isBilimit {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (g : X' ⟶ X) :
    (baseChangeQuotientCone G φ hφ g).IsBilimit := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
