/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Atlas
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets
public import ReasLib.CategoryTheory.Category.ULift
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Postcomposition
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Equivalence
public import stacks_project.Chap78.Lemma_78_20_2_Atlas
public import stacks_project.Chap78.Lemma_78_21_1_QuotientMap
public import stacks_project.Chap78.Lemma_78_21_2_IsoComma

/-!
# 2-commutative square of the iso-comma groupoid

A morphism `f : Hom G H` determines cartesian functors `[g]`, `[f]`, `[U''/R''] ⟶ 𝒮_{U'}`,
and `𝒮_{U'} ⟶ [U'/R']` over `(Sch/S)_fppf`. The invertible `2`-cell has fibre the inverse of
the `R'`-factor of a `U''`-point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits Opposite
open CategoryTheory.CategoryOfElements CategoryTheory.Bicategory
open Functor.IsFibered.InGroupoids.Stackification
open CategoryTheory.Pseudofunctor.CoGrothendieck
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace


/-- `stackInSetsULiftTotal` is the canonical two-universe lift of the total category of `𝒮_X`. -/
theorem stackInSetsULiftTotal_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    stackInSetsULiftTotal X =
      Cat.twoULift.{u + 1, u, u + 1, u + 1} (stackInSets X).total := sorry




/-- The projection of the universe-aligned `𝒮_X` is the two-universe lift of `𝒮_X`. -/
theorem stackInSetsULift_p {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (stackInSetsULift X).p = stackInSetsULiftProjection X := sorry



/-- Postcomposing the morphism-universe lift of `𝒮_X` with its inverse recovers the identity. -/
theorem stackInSetsULift.up_comp_down {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (stackInSetsULift.up X).comp (stackInSetsULift.down X) =
      CartesianBasedFunctor.id (stackInSets X).p := sorry

/-- Postcomposing the inverse morphism-universe lift of `𝒮_X` with the lift recovers the
identity. -/
theorem stackInSetsULift.down_comp_up {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (stackInSetsULift.down X).comp (stackInSetsULift.up X) =
      CartesianBasedFunctor.id (stackInSetsULift X).p := sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.GroupoidAlgebraicSpace


/-- `fppfAtlas` is the object-inclusion into `[U/_p R]` followed by fppf stackification. -/
theorem fppfAtlas_eq {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    fppfAtlas G =
      (atlasToPreQuotient G).comp (fppfQuotientStackPresentation G).comparison := sorry


/-- `fppfAtlasULift` is the morphism-universe inverse of `𝒮_U` followed by `fppfAtlas`. -/
theorem fppfAtlasULift_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    fppfAtlasULift G = (stackInSetsULift.down G.U.left).comp (fppfAtlas G) := sorry

/-- The identity-on-objects morphism from the discrete groupoid on `U` into `G`. -/
def discreteInclusion {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    Hom (discrete G.U) G where
  obj := 𝟙 G.U
  arrow := G.e
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of `discreteInclusion` is the identity of `U`. -/
theorem discreteInclusion_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (discreteInclusion G).obj = 𝟙 G.U := sorry

/-- The total functor `[U/_p U] ⟶ 𝒮_U` sending a point of the discrete prestack to the
corresponding point of `U`. -/
def discreteToStackInSetsPreFunctor {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    (preQuotient (discrete U)).total ⥤ (stackInSets U.left).total where
  obj x :=
    op ⟨op x.base, yonedaEquiv x.fiber⟩
  map {x y} g :=
    (homMk ⟨op y.base, yonedaEquiv y.fiber⟩
        ⟨op x.base, yonedaEquiv x.fiber⟩ g.base.op sorry).op
  map_id := sorry
  map_comp := sorry

/-- The cartesian `1`-morphism `[U/_p U] ⟶ 𝒮_U` induced by the identity of `U`. -/
def discreteToStackInSetsPre {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    CartesianBasedFunctor (preQuotient (discrete U)).p (stackInSets U.left).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (discreteToStackInSetsPreFunctor U) sorry)

/-- The selected stackification lift of `[U/_p U] ⟶ 𝒮_U` through `[U/_p U] ⟶ [U/U]`. -/
def discreteToStackInSetsLift {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation (discrete U)).comparison)
      (discreteToStackInSetsPre U) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (fppfQuotientStackPresentation (discrete U)).isStackification
    (discreteToStackInSetsPre U)

/-- The cartesian comparison `[U/U] ⟶ 𝒮_U` identifying the discrete quotient stack with the
stack in sets. This is the heterogeneous identification required because
`(stackInSets U.left).toGroupoids` lives in a smaller Hom-universe than
`fppfQuotientStack (discrete U)`. -/
def discreteQuotientToStackInSets {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    CartesianBasedFunctor (fppfQuotientStack (discrete U)).p (stackInSets U.left).p :=
  (discreteToStackInSetsLift U).lift

/-- Postcomposing the discrete-quotient comparison with `fppfAtlas` recovers the identity of
`[U/U]`. -/
theorem discreteQuotientToStackInSets_comp_fppfAtlas
    {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    (discreteQuotientToStackInSets U).comp (fppfAtlas (discrete U)) =
      CartesianBasedFunctor.id (fppfQuotientStack (discrete U)).p := sorry

/-- Postcomposing `fppfAtlas` of the discrete groupoid with the discrete-quotient comparison
recovers the identity of `𝒮_U`. -/
theorem fppfAtlas_comp_discreteQuotientToStackInSets
    {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    (fppfAtlas (discrete U)).comp (discreteQuotientToStackInSets U) =
      CartesianBasedFunctor.id (stackInSets U.left).p := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}

/-- The total functor `[U''/_p R''] ⟶ 𝒮_{U'}` sending a point of `U''` to `s'` of its `R'`-factor. -/
def isoCommaToTargetPreFunctor (f : Hom G H) :
    (preQuotient (isoComma f)).total ⥤ (stackInSets H.U.left).total where
  obj x :=
    op ⟨op x.base, yonedaEquiv (x.fiber ≫ (isoCommaToTargetObject f).left)⟩
  map {x y} g :=
    (homMk ⟨op y.base, yonedaEquiv (y.fiber ≫ (isoCommaToTargetObject f).left)⟩
        ⟨op x.base, yonedaEquiv (x.fiber ≫ (isoCommaToTargetObject f).left)⟩ g.base.op sorry).op
  map_id := sorry
  map_comp := sorry

/-- The cartesian `1`-morphism `[U''/_p R''] ⟶ 𝒮_{U'}` induced by `U'' ⟶ U'`. -/
def isoCommaToTargetPre (f : Hom G H) :
    CartesianBasedFunctor (preQuotient (isoComma f)).p (stackInSets H.U.left).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (isoCommaToTargetPreFunctor f) sorry)

/-- The selected stackification lift of `[U''/_p R''] ⟶ 𝒮_{U'}` through `[U''/_p R''] ⟶ [U''/R'']`. -/
def isoCommaToTargetLift (f : Hom G H) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation (isoComma f)).comparison)
      (isoCommaToTargetPre f) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (fppfQuotientStackPresentation (isoComma f)).isStackification (isoCommaToTargetPre f)

/-- The cartesian `1`-morphism `[U''/R''] ⟶ 𝒮_{U'}` obtained by lifting the prestack map. -/
def isoCommaToTarget (f : Hom G H) :
    CartesianBasedFunctor (fppfQuotientStack (isoComma f)).p (stackInSets H.U.left).p :=
  (isoCommaToTargetLift f).lift

/-- The `R'`-factor of a prestack point of `U''`. -/
def isoCommaSpacePointFactor (f : Hom G H)
    (x : (preQuotient (isoComma f)).total) :
    ofOver x.base ⟶ H.R.left :=
  x.fiber ≫ (pullback.snd f.obj H.t).left

/-- The fibre morphism of `[U'/_p R']` associated to the inverse of the `R'`-factor. -/
def isoCommaPreHom (f : Hom G H) (x : (preQuotient (isoComma f)).total) :
    ((prestackMap (isoCommaHom f)).comp (prestackMap f)).toFunctor.obj x ⟶
      ((isoCommaToTargetPre f).comp (atlasToPreQuotient H)).toFunctor.obj x where
  base := 𝟙 ((((prestackMap (isoCommaHom f)).comp (prestackMap f)).toFunctor.obj x).base)
  fiber :=
    SpacePointHom.ofArrow (isoCommaSpacePointFactor f x ≫ H.i.left) sorry sorry

/-- The inverse fibre morphism, whose underlying arrow is the `R'`-factor itself. -/
def isoCommaPreInvHom (f : Hom G H) (x : (preQuotient (isoComma f)).total) :
    ((isoCommaToTargetPre f).comp (atlasToPreQuotient H)).toFunctor.obj x ⟶
      ((prestackMap (isoCommaHom f)).comp (prestackMap f)).toFunctor.obj x where
  base := 𝟙 ((((isoCommaToTargetPre f).comp (atlasToPreQuotient H)).toFunctor.obj x).base)
  fiber := SpacePointHom.ofArrow (isoCommaSpacePointFactor f x) sorry sorry

/-- The prestack `2`-isomorphism `[g]_p ≫ [f]_p ≅ toTarget_p ≫ atlas_p`. -/
def isoCommaPreIso (f : Hom G H) :
    (prestackMap (isoCommaHom f)).comp (prestackMap f) ≅
      (isoCommaToTargetPre f).comp (atlasToPreQuotient H) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ isoCommaPreHom f x
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ isoCommaPreInvHom f x
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The stacked `2`-isomorphism obtained by applying stackification of `[U'/R']` to the
prestack components of `isoCommaPreIso`. -/
def isoCommaPreStackIso (f : Hom G H) :
    (prestackMap (isoCommaHom f)).comp (prestackToQuotient f) ≅
      (isoCommaToTargetPre f).comp (fppfAtlas H) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦
          (fppfQuotientStackPresentation H).comparison.toFunctor.map (isoCommaPreHom f x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦
          (fppfQuotientStackPresentation H).comparison.toFunctor.map (isoCommaPreInvHom f x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identity-on-objects associator identifying `((i ≫ [g]) ≫ [f])` with `i ≫ ([g] ≫ [f])`. -/
def isoCommaLeftAssoc (f : Hom G H) :
    ((fppfQuotientStackPresentation (isoComma f)).comparison.comp
        (quotientStackMap (isoCommaHom f))).comp (quotientStackMap f) ≅
      (fppfQuotientStackPresentation (isoComma f)).comparison.comp
        ((quotientStackMap (isoCommaHom f)).comp (quotientStackMap f)) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (quotientStackMap (isoCommaHom f))).comp (quotientStackMap f)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (quotientStackMap (isoCommaHom f))).comp (quotientStackMap f)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identity-on-objects associator identifying `(prestackToQuotient g) ≫ [f]` with
`[g]_p ≫ ((i_G) ≫ [f])`. -/
def isoCommaLeftPreAssoc (f : Hom G H) :
    (prestackToQuotient (isoCommaHom f)).comp (quotientStackMap f) ≅
      (prestackMap (isoCommaHom f)).comp
        ((fppfQuotientStackPresentation G).comparison.comp (quotientStackMap f)) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 (((prestackToQuotient (isoCommaHom f)).comp (quotientStackMap f)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 (((prestackToQuotient (isoCommaHom f)).comp (quotientStackMap f)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identity-on-objects associator identifying `((i ≫ toTarget) ≫ atlas)` with
`i ≫ (toTarget ≫ atlas)`. -/
def isoCommaRightAssoc (f : Hom G H) :
    ((fppfQuotientStackPresentation (isoComma f)).comparison.comp
        (isoCommaToTarget f)).comp (fppfAtlas H) ≅
      (fppfQuotientStackPresentation (isoComma f)).comparison.comp
        ((isoCommaToTarget f).comp (fppfAtlas H)) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (isoCommaToTarget f)).comp (fppfAtlas H)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (isoCommaToTarget f)).comp (fppfAtlas H)).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The stackification lift of `[g]_p ≫ [f]_p` whose lift is `[g] ≫ [f]`. -/
def isoCommaLeftLift (f : Hom G H) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation (isoComma f)).comparison)
      ((isoCommaToTargetPre f).comp (fppfAtlas H)) where
  lift := (quotientStackMap (isoCommaHom f)).comp (quotientStackMap f)
  comparison :=
    (isoCommaLeftAssoc f).symm ≪≫
      (CartesianBasedFunctor.postcomp (preQuotient (isoComma f)).p
          (quotientStackMap f)).mapIso (quotientStackMap_comp (isoCommaHom f)) ≪≫
      isoCommaLeftPreAssoc f ≪≫
      (CartesianBasedFunctor.precomp (fppfQuotientStack H).p
          (prestackMap (isoCommaHom f))).mapIso (quotientStackMap_comp f) ≪≫
      isoCommaPreStackIso f

/-- The stackification lift of `toTarget_p ≫ atlas` whose lift is `toTarget ≫ atlas`. -/
def isoCommaRightLift (f : Hom G H) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation (isoComma f)).comparison)
      ((isoCommaToTargetPre f).comp (fppfAtlas H)) where
  lift := (isoCommaToTarget f).comp (fppfAtlas H)
  comparison :=
    (isoCommaRightAssoc f).symm ≪≫
      (CartesianBasedFunctor.postcomp (preQuotient (isoComma f)).p (fppfAtlas H)).mapIso
        (isoCommaToTargetLift f).comparison

/-- The stacked `2`-isomorphism `[g] ≫ [f] ≅ toTarget ≫ atlas`. -/
def isoCommaIso (f : Hom G H) :
    (quotientStackMap (isoCommaHom f)).comp (quotientStackMap f) ≅
      (isoCommaToTarget f).comp (fppfAtlas H) :=
  CartesianBasedFunctor.IsStackification.LiftChoice.comparisonIso
    (fppfQuotientStackPresentation (isoComma f)).isStackification
    (isoCommaLeftLift f) (isoCommaRightLift f)

/-- The cartesian `1`-morphism `[U''/R''] ⟶ 𝒮_{U'}` after aligning `𝒮_{U'}` to the Hom-universe
of `[U'/R']`. -/
def isoCommaToTargetULift (f : Hom G H) :
    CartesianBasedFunctor (fppfQuotientStack (isoComma f)).p (stackInSetsULift H.U.left).p :=
  (isoCommaToTarget f).comp (stackInSetsULift.up H.U.left)

/-- `isoCommaToTargetULift` is `isoCommaToTarget` followed by the morphism-universe lift. -/
theorem isoCommaToTargetULift_eq (f : Hom G H) :
    isoCommaToTargetULift f =
      (isoCommaToTarget f).comp (stackInSetsULift.up H.U.left) := sorry

/-- Comparison identifying `toTarget ≫ atlas` with the universe-aligned composite into `𝒮_{U'}`,
using the unit of the two-universe equivalence of `𝒮_{U'}`. -/
def isoCommaAlignedAssoc (f : Hom G H) :
    (isoCommaToTarget f).comp (fppfAtlas H) ≅
      (isoCommaToTargetULift f).comp (fppfAtlasULift H) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (fppfQuotientStack (isoComma f)).total) ↦
          (fppfAtlas H).toFunctor.map
            ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
                (stackInSets H.U.left).total).unitIso.hom.app
              ((isoCommaToTarget f).toFunctor.obj x))
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (fppfQuotientStack (isoComma f)).total) ↦
          (fppfAtlas H).toFunctor.map
            ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
                (stackInSets H.U.left).total).unitIso.inv.app
              ((isoCommaToTarget f).toFunctor.obj x))
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The stacked `2`-isomorphism `[g] ≫ [f] ≅ left ≫ fppfAtlas` after aligning `𝒮_{U'}`. -/
def isoCommaIsoULift (f : Hom G H) :
    (quotientStackMap (isoCommaHom f)).comp (quotientStackMap f) ≅
      (isoCommaToTargetULift f).comp (fppfAtlasULift H) :=
  isoCommaIso f ≪≫ isoCommaAlignedAssoc f

/-- The fibre of the prestack cell at a `U''`-point is the inverse of the `R'`-factor. -/
theorem isoCommaIso_hom_app (f : Hom G H) (x : (preQuotient (isoComma f)).total) :
    (isoCommaPreHom f x).fiber.arrow = isoCommaSpacePointFactor f x ≫ H.i.left := sorry

/-- The groupoid morphism `G'' ⟶ (U')_disc` with object map `(u, r') ↦ s'(r')`. -/
def isoCommaToDiscrete (f : Hom G H) : Hom (isoComma f) (discrete H.U) where
  obj := isoCommaToTargetObject f
  arrow := pullback.snd (G.s ≫ f.obj) H.t ≫ H.s
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of `isoCommaToDiscrete` is `U'' ⟶ U'`. -/
theorem isoCommaToDiscrete_obj (f : Hom G H) :
    (isoCommaToDiscrete f).obj = isoCommaToTargetObject f := sorry

/-- The fibre morphism of `[U'/_p R']` associated to the inverse of the `R'`-factor, landing
in the discrete-atlas presentation of `𝒮_{U'}`. -/
def isoCommaDiscretePreHom (f : Hom G H) (x : (preQuotient (isoComma f)).total) :
    ((prestackMap (isoCommaHom f)).comp (prestackMap f)).toFunctor.obj x ⟶
      ((prestackMap (isoCommaToDiscrete f)).comp
        (prestackMap (discreteInclusion H))).toFunctor.obj x where
  base := 𝟙 _
  fiber := SpacePointHom.ofArrow (isoCommaSpacePointFactor f x ≫ H.i.left) sorry sorry

/-- The inverse fibre morphism for the discrete-atlas presentation, whose underlying arrow is
the `R'`-factor itself. -/
def isoCommaDiscretePreInvHom (f : Hom G H) (x : (preQuotient (isoComma f)).total) :
    ((prestackMap (isoCommaToDiscrete f)).comp
        (prestackMap (discreteInclusion H))).toFunctor.obj x ⟶
      ((prestackMap (isoCommaHom f)).comp (prestackMap f)).toFunctor.obj x where
  base := 𝟙 _
  fiber := SpacePointHom.ofArrow (isoCommaSpacePointFactor f x) sorry sorry

/-- The prestack `2`-isomorphism `[g]_p ≫ [f]_p ≅ [toDiscrete]_p ≫ [discreteInclusion]_p`. -/
def isoCommaDiscretePreIso (f : Hom G H) :
    (prestackMap (isoCommaHom f)).comp (prestackMap f) ≅
      (prestackMap (isoCommaToDiscrete f)).comp (prestackMap (discreteInclusion H)) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ isoCommaDiscretePreHom f x
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ isoCommaDiscretePreInvHom f x
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The whiskered discrete prestack cell `[g]_p ≫ [f] ≅ [toDiscrete]_p ≫ [discreteInclusion]`. -/
def isoCommaDiscretePreStackIso (f : Hom G H) :
    (prestackMap (isoCommaHom f)).comp (prestackToQuotient f) ≅
      (prestackMap (isoCommaToDiscrete f)).comp (prestackToQuotient (discreteInclusion H)) :=
  (CartesianBasedFunctor.postcomp (preQuotient (isoComma f)).p
      (fppfQuotientStackPresentation H).comparison).mapIso (isoCommaDiscretePreIso f)

/-- Identity-on-objects associator for the discrete right composite. -/
def isoCommaDiscreteRightAssoc (f : Hom G H) :
    ((fppfQuotientStackPresentation (isoComma f)).comparison.comp
        (quotientStackMap (isoCommaToDiscrete f))).comp
      (quotientStackMap (discreteInclusion H)) ≅
      (fppfQuotientStackPresentation (isoComma f)).comparison.comp
        ((quotientStackMap (isoCommaToDiscrete f)).comp
          (quotientStackMap (discreteInclusion H))) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (quotientStackMap (isoCommaToDiscrete f))).comp
            (quotientStackMap (discreteInclusion H))).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (quotientStackMap (isoCommaToDiscrete f))).comp
            (quotientStackMap (discreteInclusion H))).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identity-on-objects associator identifying `(prestackToQuotient toDiscrete) ≫ [discInc]`
with `[toDiscrete]_p ≫ ((i) ≫ [discInc])`. -/
def isoCommaDiscreteLeftPreAssoc (f : Hom G H) :
    (prestackToQuotient (isoCommaToDiscrete f)).comp
        (quotientStackMap (discreteInclusion H)) ≅
      (prestackMap (isoCommaToDiscrete f)).comp
        ((fppfQuotientStackPresentation (discrete H.U)).comparison.comp
          (quotientStackMap (discreteInclusion H))) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 (((prestackToQuotient (isoCommaToDiscrete f)).comp
            (quotientStackMap (discreteInclusion H))).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 (((prestackToQuotient (isoCommaToDiscrete f)).comp
            (quotientStackMap (discreteInclusion H))).toFunctor.obj x)
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The stackification lift of the discrete-atlas composite. -/
def isoCommaDiscreteRightLift (f : Hom G H) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation (isoComma f)).comparison)
      ((prestackMap (isoCommaHom f)).comp (prestackToQuotient f)) where
  lift := (quotientStackMap (isoCommaToDiscrete f)).comp
    (quotientStackMap (discreteInclusion H))
  comparison :=
    (isoCommaDiscreteRightAssoc f).symm ≪≫
      (CartesianBasedFunctor.postcomp (preQuotient (isoComma f)).p
          (quotientStackMap (discreteInclusion H))).mapIso
        (quotientStackMap_comp (isoCommaToDiscrete f)) ≪≫
      isoCommaDiscreteLeftPreAssoc f ≪≫
      (CartesianBasedFunctor.precomp (fppfQuotientStack H).p
          (prestackMap (isoCommaToDiscrete f))).mapIso
        (quotientStackMap_comp (discreteInclusion H)) ≪≫
      (isoCommaDiscretePreStackIso f).symm

/-- The stackification lift of `[g] ≫ [f]` against the same prestack composite. -/
def isoCommaDiscreteLeftLift (f : Hom G H) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation (isoComma f)).comparison)
      ((prestackMap (isoCommaHom f)).comp (prestackToQuotient f)) where
  lift := (quotientStackMap (isoCommaHom f)).comp (quotientStackMap f)
  comparison :=
    (isoCommaLeftAssoc f).symm ≪≫
      (CartesianBasedFunctor.postcomp (preQuotient (isoComma f)).p
          (quotientStackMap f)).mapIso (quotientStackMap_comp (isoCommaHom f)) ≪≫
      isoCommaLeftPreAssoc f ≪≫
      (CartesianBasedFunctor.precomp (fppfQuotientStack H).p
          (prestackMap (isoCommaHom f))).mapIso (quotientStackMap_comp f)

/-- The stacked `2`-isomorphism `[g] ≫ [f] ≅ [toDiscrete] ≫ [discreteInclusion]`. -/
def isoCommaDiscreteIso (f : Hom G H) :
    (quotientStackMap (isoCommaHom f)).comp (quotientStackMap f) ≅
      (quotientStackMap (isoCommaToDiscrete f)).comp
        (quotientStackMap (discreteInclusion H)) :=
  CartesianBasedFunctor.IsStackification.LiftChoice.comparisonIso
    (fppfQuotientStackPresentation (isoComma f)).isStackification
    (isoCommaDiscreteLeftLift f) (isoCommaDiscreteRightLift f)

/-- The right leg `[f] : [U/R] ⟶ [U'/R']` as a morphism of stacks in groupoids. -/
def isoCommaConeRight (f : Hom G H) :
    fppfQuotientStack G ⟶ fppfQuotientStack H :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (quotientStackMap f).toBasedFunctor)

/-- The first projection `[g] : [U''/R''] ⟶ [U/R]` as a morphism of stacks in groupoids. -/
def isoCommaConeFst (f : Hom G H) :
    fppfQuotientStack (isoComma f) ⟶ fppfQuotientStack G :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor
      (quotientStackMap (isoCommaHom f)).toBasedFunctor)

/-- The left leg `[U''/R''] ⟶ 𝒮_{U'}` of the source square, after aligning `𝒮_{U'}` to the
Hom-universe of `[U'/R']`. -/
def isoCommaConeSnd (f : Hom G H) :
    fppfQuotientStack (isoComma f) ⟶ stackInSetsULift H.U.left :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor
      (isoCommaToTargetULift f).toBasedFunctor)

/-- The bottom atlas `𝒮_{U'} ⟶ [U'/R']` of the source square, after aligning `𝒮_{U'}`. -/
def isoCommaConeBottom (_ : Hom G H) :
    stackInSetsULift H.U.left ⟶ fppfQuotientStack H :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (fppfAtlasULift H).toBasedFunctor)

/-- The packaged `2`-isomorphism `[g] ≫ [f] ≅ left ≫ fppfAtlas` of the iso-comma square. -/
def isoCommaConeIso (f : Hom G H) :
    isoCommaConeFst f ≫ isoCommaConeRight f ≅
      isoCommaConeSnd f ≫ isoCommaConeBottom f :=
  StackOver.Groupoids.Hom.isoMk
    (FiberedCategoryOver.Groupoids.BasedFunctorIso.lift
      (CartesianBasedFunctor.toBasedIso (isoCommaIsoULift f)))

/-- The `2`-commutative square with apex `[U''/R'']`, right leg `[f] : [U/R] ⟶ [U'/R']`,
left leg `[U''/R''] ⟶ 𝒮_{U'}`, and bottom atlas `𝒮_{U'} ⟶ [U'/R']`. -/
def isoCommaCone (f : Hom G H) :
    PseudoPullbackCone (isoCommaConeRight f) (isoCommaConeBottom f) where
  pt := fppfQuotientStack (isoComma f)
  fst := isoCommaConeFst f
  snd := isoCommaConeSnd f
  iso := isoCommaConeIso f

/-- The apex of `isoCommaCone f` is `[U''/R'']`. -/
theorem isoCommaCone_pt (f : Hom G H) :
    (isoCommaCone f).pt = fppfQuotientStack (isoComma f) := sorry

/-- The first projection of `isoCommaCone f` is `[g]`. -/
theorem isoCommaCone_fst (f : Hom G H) :
    (isoCommaCone f).fst = isoCommaConeFst f := sorry

/-- The second projection of `isoCommaCone f` is the left leg `[U''/R''] ⟶ 𝒮_{U'}`. -/
theorem isoCommaCone_snd (f : Hom G H) :
    (isoCommaCone f).snd = isoCommaConeSnd f := sorry

/-- The `2`-cell of `isoCommaCone f` is `isoCommaConeIso f`. -/
theorem isoCommaCone_iso (f : Hom G H) :
    (isoCommaCone f).iso = isoCommaConeIso f := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
