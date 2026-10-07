module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_28_1_Hom
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf
public import stacks_project.Chap76.Lemma_76_5_3_Map
public import stacks_project.Chap76.Lemma_76_9_2_Structure
public import stacks_project.Chap76.Lemma_76_18_1_Thickening

/-!
# Differences of morphisms of first-order thickenings of algebraic spaces

Two morphisms of first-order thickenings over `B` with the same reduced map and the
same Lemma 76.5.3 comparison `Hom.Conormal.map` differ by an `𝒪_B`-derivation
`𝒪_Y ⟶ a_* C_{X/X'}`. The inverse-image form of `(a')^♯ - (b')^♯` on
`X_spaces,étale` recovers the source composite
`𝒪_{Y'} ⟶ 𝒪_Y ⟶^D a_* C_{X/X'} ⟶ a_* 𝒪_{X'}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace.Thickening
open Sheaf.InternalModule RingedSite.ToposHom
noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}}

/-- Forget ring-valued sheaves on the spaces-étale site to abelian groups. -/
abbrev forgetSpacesRing (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) RingCat.{u} ⥤
      Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u} :=
  sheafCompose (spacesEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u})

/-- `forgetSpacesRing X` is sheaf composition with `forget₂ RingCat AddCommGrpCat`. -/
theorem forgetSpacesRing_eq (X : AlgebraicSpace S) :
    forgetSpacesRing X =
      sheafCompose (spacesEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u}) :=
  rfl

/-- Restriction of abelian sheaves from `X_spaces,étale` to `X_étale`. -/
abbrev restrictSpacesAdd (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  (smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
    (smallEtaleTopology X) (spacesEtaleTopology X)

/-- `restrictSpacesAdd X` is continuous pushforward along the small étale inclusion. -/
theorem restrictSpacesAdd_eq (X : AlgebraicSpace S) :
    restrictSpacesAdd X =
      (smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
        (smallEtaleTopology X) (spacesEtaleTopology X) :=
  rfl

/-- Left Kan extensions of abelian-group presheaves along the opposite of étale base
change exist on the small étale sites of algebraic spaces. -/
instance etaleBaseChange_op_hasLeftKanExtension_addCommGrpCat
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : (smallEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (etaleBaseChange f).op.HasLeftKanExtension F :=
  sorry

/-- Abelian-group-valued weak sheafification exists on the étale site of algebraic
spaces. -/
instance spacesEtaleTopology_hasWeakSheafify_addCommGrpCat (X : AlgebraicSpace S) :
    HasWeakSheafify (spacesEtaleTopology X) AddCommGrpCat.{u} :=
  sorry

/-- The opposite of the small étale inclusion has pointwise right Kan extensions on
abelian-group-valued presheaves. -/
instance smallEtaleInclusion_op_hasPointwiseRightKanExtension_addCommGrpCat_u
    (X : AlgebraicSpace S) (P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Inverse image of abelian sheaves along a morphism of algebraic spaces. -/
abbrev addInverseImage {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  sheafInverseImage AddCommGrpCat.{u} f

/-- `addInverseImage f` is `sheafInverseImage` of abelian groups. -/
theorem addInverseImage_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    addInverseImage f = sheafInverseImage AddCommGrpCat.{u} f :=
  rfl

/-- Direct image of abelian sheaves along a morphism of algebraic spaces. -/
abbrev addPushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u} :=
  sheafPushforward AddCommGrpCat.{u} f

/-- `addPushforward f` is `sheafPushforward` of abelian groups. -/
theorem addPushforward_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    addPushforward f = sheafPushforward AddCommGrpCat.{u} f :=
  rfl

/-- Geometric inverse image of abelian sheaves is left adjoint to direct image. -/
def addInverseImageAdjunction {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    addInverseImage f ⊣ addPushforward f :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (etaleBaseChange f) AddCommGrpCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology X)).comp
    ((smallEtaleInclusion X).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (smallEtaleTopology X) (spacesEtaleTopology X))

/-- Unfolding of `addInverseImageAdjunction`. -/
theorem addInverseImageAdjunction_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    addInverseImageAdjunction f =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (etaleBaseChange f) AddCommGrpCat.{u}
          (smallEtaleTopology Y) (spacesEtaleTopology X)).comp
        ((smallEtaleInclusion X).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
          (smallEtaleTopology X) (spacesEtaleTopology X)) :=
  rfl

/-- The inverse-image form of `(a')^♯ - (b')^♯` on `X_spaces,étale`. -/
def structureMapDifference {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    (ha' : iX ≫ a' = a ≫ iY) (hb' : iX ≫ b' = a ≫ iY) :
    (forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY) ⟶
      (forgetSpacesRing X).obj (closedStructureSheaf iX) :=
  (forgetSpacesRing X).map (structureMap_transported iX iY a a' ha') -
    (forgetSpacesRing X).map (structureMap_transported iX iY a b' hb')

/-- Unfolding of `structureMapDifference`. -/
theorem structureMapDifference_eq {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    (ha' : iX ≫ a' = a ≫ iY) (hb' : iX ≫ b' = a ≫ iY) :
    structureMapDifference iX iY a a' b' ha' hb' =
      (forgetSpacesRing X).map (structureMap_transported iX iY a a' ha') -
        (forgetSpacesRing X).map (structureMap_transported iX iY a b' hb') :=
  rfl

/-- Sectionwise values of `(a')^♯ - (b')^♯` on `X_spaces,étale`. -/
def structureMapDifference_apply {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    (ha' : iX ≫ a' = a ≫ iY) (hb' : iX ≫ b' = a ≫ iY)
    (V : (spacesEtaleSite X)ᵒᵖ)
    (x : (inverseImageClosedStructureSheaf a iY).obj.obj V) :
    (closedStructureSheaf iX).obj.obj V :=
  (structureMap_transported iX iY a a' ha').hom.app V x -
    (structureMap_transported iX iY a b' hb').hom.app V x

/-- Unfolding of `structureMapDifference_apply`. -/
theorem structureMapDifference_apply_eq {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    (ha' : iX ≫ a' = a ≫ iY) (hb' : iX ≫ b' = a ≫ iY)
    (V : (spacesEtaleSite X)ᵒᵖ)
    (x : (inverseImageClosedStructureSheaf a iY).obj.obj V) :
    structureMapDifference_apply iX iY a a' b' ha' hb' V x =
      (structureMap_transported iX iY a a' ha').hom.app V x -
        (structureMap_transported iX iY a b' hb').hom.app V x :=
  rfl

/-- The additive difference of `(a')^♯` and `(b')^♯`, restricted to `X_étale`. -/
def structureMapDifference_restrict {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    (ha' : iX ≫ a' = a ≫ iY) (hb' : iX ≫ b' = a ≫ iY) :
    (restrictSpacesAdd X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY)) ⟶
      (restrictSpacesAdd X).obj ((forgetSpacesRing X).obj (closedStructureSheaf iX)) :=
  (restrictSpacesAdd X).map (structureMapDifference iX iY a a' b' ha' hb')

/-- Unfolding of `structureMapDifference_restrict`. -/
theorem structureMapDifference_restrict_eq {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    (ha' : iX ≫ a' = a ≫ iY) (hb' : iX ≫ b' = a ≫ iY) :
    structureMapDifference_restrict iX iY a a' b' ha' hb' =
      (restrictSpacesAdd X).map (structureMapDifference iX iY a a' b' ha' hb') :=
  rfl

/-- The first-order action `I ⊗ I ⟶ I` followed by the identity on `I` vanishes. -/
theorem firstOrderIdealAction_comp_id {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    Modules.idealAction (Hom.idealSheafSubobject i) (Hom.idealSheaf i) ≫
      𝟙 (Hom.idealSheaf i) = 0 :=
  sorry

/-- The inverse of `I ⟶ I/I²` on a first-order thickening, as cokernel descent of the
identity along the vanishing action `I ⊗ I ⟶ I`. -/
def firstOrderQuotientInv {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i) ⟶
      Hom.idealSheaf i :=
  cokernel.desc
    (Modules.idealAction (Hom.idealSheafSubobject i) (Hom.idealSheaf i))
    (𝟙 (Hom.idealSheaf i)) (firstOrderIdealAction_comp_id i)

/-- Unfolding of `firstOrderQuotientInv`. -/
theorem firstOrderQuotientInv_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    firstOrderQuotientInv i =
      cokernel.desc
        (Modules.idealAction (Hom.idealSheafSubobject i) (Hom.idealSheaf i))
        (𝟙 (Hom.idealSheaf i)) (firstOrderIdealAction_comp_id i) :=
  rfl

/-- The module inclusion `I/I² ⟶ 𝒪` of a first-order thickening. -/
def firstOrderIdealIncl {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i) ⟶
      SheafOfModules.unit (structureSheaf X) :=
  firstOrderQuotientInv i ≫ Hom.idealSheafι i

/-- Unfolding of `firstOrderIdealIncl`. -/
theorem firstOrderIdealIncl_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    firstOrderIdealIncl i = firstOrderQuotientInv i ≫ Hom.idealSheafι i :=
  rfl

/-- The underlying presheaf of an `𝒪_X`-module as a module over the commutative
structure sheaf. -/
abbrev toCommPresheaf {X : AlgebraicSpace S} (F : X.Modules) :
    PresheafOfModules
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat) :=
  (SheafOfModules.forget (structureSheaf X)).obj F

/-- `toCommPresheaf F` is the underlying presheaf of `F`. -/
theorem toCommPresheaf_eq {X : AlgebraicSpace S} (F : X.Modules) :
    toCommPresheaf F = (SheafOfModules.forget (structureSheaf X)).obj F :=
  rfl

/-- The type of `𝒪_B`-derivations `𝒪_Y ⟶ F` relative to the inverse-image structure
map of `sY`. This is the Conormal-import form of `Hom.derivations`, using the
definitional identification of `commStructureSheaf` with `structureSheaf`. -/
abbrev derivations {Y B : AlgebraicSpace S} (sY : Y ⟶ B) (F : Y.Modules) :=
  (toCommPresheaf F).Derivation' (commInverseImageStructureSheafMap sY).hom

/-- `derivations sY F` is the type of relative derivations of
`commInverseImageStructureSheafMap sY`. -/
theorem derivations_eq {Y B : AlgebraicSpace S} (sY : Y ⟶ B) (F : Y.Modules) :
    derivations sY F =
      (toCommPresheaf F).Derivation' (commInverseImageStructureSheafMap sY).hom :=
  rfl

/-- An `𝒪_B`-derivation annihilates the inverse-image structure map of `sY`. -/
theorem derivation_d_app {Y B : AlgebraicSpace S} (sY : Y ⟶ B)
    (F : Y.Modules) (D : derivations sY F) {U : (smallEtaleSite Y)ᵒᵖ}
    (a : (commInverseImageStructureSheaf sY).obj.obj U) :
    D.d ((commInverseImageStructureSheafMap sY).hom.app U a) = 0 :=
  sorry

/-- Naturality of the objectwise additive maps underlying a relative derivation. -/
theorem derivationAdditiveMap_naturality {Y B : AlgebraicSpace S} (sY : Y ⟶ B)
    (F : Y.Modules) (D : derivations sY F)
    {U V : (smallEtaleSite Y)ᵒᵖ} (g : U ⟶ V) :
    ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf Y)).obj.map g ≫ AddCommGrpCat.ofHom D.d =
      AddCommGrpCat.ofHom D.d ≫
        ((SheafOfModules.toSheaf (structureSheaf Y)).obj F).obj.map g :=
  sorry

/-- The underlying presheaf morphism of a relative derivation, assembled from `D.d`. -/
def derivationAdditiveMap_presheaf {Y B : AlgebraicSpace S} (sY : Y ⟶ B)
    (F : Y.Modules) (D : derivations sY F) :
    ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf Y)).obj ⟶
      ((SheafOfModules.toSheaf (structureSheaf Y)).obj F).obj :=
  { app := fun _ ↦ AddCommGrpCat.ofHom D.d
    naturality := fun _ _ g ↦ derivationAdditiveMap_naturality sY F D g }

/-- Unfolding of `derivationAdditiveMap_presheaf`. -/
theorem derivationAdditiveMap_presheaf_eq {Y B : AlgebraicSpace S} (sY : Y ⟶ B)
    (F : Y.Modules) (D : derivations sY F) :
    derivationAdditiveMap_presheaf sY F D =
      { app := fun _ ↦ AddCommGrpCat.ofHom D.d
        naturality := fun _ _ g ↦ derivationAdditiveMap_naturality sY F D g } :=
  rfl

/-- The additive sheaf morphism `𝒪_Y ⟶ F` induced by the objectwise maps `D.d`. -/
def derivationAdditiveMap {Y B : AlgebraicSpace S} (sY : Y ⟶ B) (F : Y.Modules)
    (D : derivations sY F) :
    (sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf Y) ⟶
      (SheafOfModules.toSheaf (structureSheaf Y)).obj F :=
  InducedCategory.homMk (derivationAdditiveMap_presheaf sY F D)

/-- Unfolding of `derivationAdditiveMap`. -/
theorem derivationAdditiveMap_eq {Y B : AlgebraicSpace S} (sY : Y ⟶ B)
    (F : Y.Modules) (D : derivations sY F) :
    derivationAdditiveMap sY F D =
      InducedCategory.homMk (derivationAdditiveMap_presheaf sY F D) :=
  rfl

/-- Inverse image of `iY^♯ : 𝒪_{Y'} ⟶ 𝒪_Y` along `a`, on `X_spaces,étale`. -/
def inverseImageRestriction {X Y Y' : AlgebraicSpace S} (a : X ⟶ Y) (iY : Y ⟶ Y') :
    inverseImageClosedStructureSheaf a iY ⟶
      (spacesRingedToposHom a).toTopos.ringInverseImage.obj (spacesStructureSheaf Y) :=
  (spacesRingedToposHom a).toTopos.ringInverseImage.map
    (closedStructureSheaf_structureMap iY)

/-- Unfolding of `inverseImageRestriction`. -/
theorem inverseImageRestriction_eq {X Y Y' : AlgebraicSpace S} (a : X ⟶ Y)
    (iY : Y ⟶ Y') :
    inverseImageRestriction a iY =
      (spacesRingedToposHom a).toTopos.ringInverseImage.map
        (closedStructureSheaf_structureMap iY) :=
  rfl

/-- Forgetful functor from abelian sheaves to type-valued sheaves on `X_étale`. -/
abbrev forgetSpacesAddType (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (smallEtaleTopology X) (Type u) :=
  sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})

/-- `forgetSpacesAddType X` is sheaf composition with `forget AddCommGrpCat`. -/
theorem forgetSpacesAddType_eq (X : AlgebraicSpace S) :
    forgetSpacesAddType X =
      sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u}) :=
  rfl

/-- The underlying type-valued sheaf of an `𝒪_X`-module agrees with forgetting the
additive sheaf `toSheaf`. -/
def toSheafUnderlyingIso (X : AlgebraicSpace S) (F : X.Modules) :
    (forgetSpacesAddType X).obj ((SheafOfModules.toSheaf (structureSheaf X)).obj F) ≅
      (ToInternal.underlying (structureSheaf X)).obj F where
  hom := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  inv := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Unfolding of the forward map of `toSheafUnderlyingIso`. -/
theorem toSheafUnderlyingIso_hom_eq (X : AlgebraicSpace S) (F : X.Modules) :
    (toSheafUnderlyingIso X F).hom =
      { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } } :=
  rfl

/-- Restriction `𝒪_{Y'} ⟶ 𝒪_Y` pulled to `X_étale`. -/
def pulledRestriction {X Y Y' : AlgebraicSpace S} (a : X ⟶ Y) (iY : Y ⟶ Y') :
    (restrictSpacesAdd X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY)) ⟶
      (restrictSpacesAdd X).obj
        ((forgetSpacesRing X).obj
          ((spacesRingedToposHom a).toTopos.ringInverseImage.obj
            (spacesStructureSheaf Y))) :=
  (restrictSpacesAdd X).map ((forgetSpacesRing X).map (inverseImageRestriction a iY))

/-- Unfolding of `pulledRestriction`. -/
theorem pulledRestriction_eq {X Y Y' : AlgebraicSpace S} (a : X ⟶ Y) (iY : Y ⟶ Y') :
    pulledRestriction a iY =
      (restrictSpacesAdd X).map
        ((forgetSpacesRing X).map (inverseImageRestriction a iY)) :=
  rfl

/-- Inverse image of the additive sheaf map induced by `D.d`. -/
def pulledDerivation {X Y B : AlgebraicSpace S} (sY : Y ⟶ B) (a : X ⟶ Y)
    {F : X.Modules} (D : derivations sY ((Modules.pushforward a).obj F)) :
    (addInverseImage a).obj
        ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
          (structureSheaf Y)) ⟶
      (addInverseImage a).obj
        ((SheafOfModules.toSheaf (structureSheaf Y)).obj
          ((Modules.pushforward a).obj F)) :=
  (addInverseImage a).map
    (derivationAdditiveMap sY ((Modules.pushforward a).obj F) D)

/-- Unfolding of `pulledDerivation`. -/
theorem pulledDerivation_eq {X Y B : AlgebraicSpace S} (sY : Y ⟶ B) (a : X ⟶ Y)
    {F : X.Modules} (D : derivations sY ((Modules.pushforward a).obj F)) :
    pulledDerivation sY a D =
      (addInverseImage a).map
        (derivationAdditiveMap sY ((Modules.pushforward a).obj F) D) :=
  rfl

/-- Named comparison from the underlying sheaf of `a_* F` to the geometric direct image
of the underlying sheaf of `F`. -/
def modulePushforwardForgetHom {X Y : AlgebraicSpace S} (a : X ⟶ Y) (F : X.Modules) :
    (ToInternal.underlying (structureSheaf Y)).obj ((Modules.pushforward a).obj F) ⟶
      (typePushforward a).obj ((ToInternal.underlying (structureSheaf X)).obj F) :=
  (ModulePushforward.forgetIso (ringedToposHom a)).hom.app F

/-- Unfolding of `modulePushforwardForgetHom`. -/
theorem modulePushforwardForgetHom_eq {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : X.Modules) :
    modulePushforwardForgetHom a F =
      (ModulePushforward.forgetIso (ringedToposHom a)).hom.app F :=
  rfl

/-- Forgetting abelian groups preserves the right Kan extensions that define cocontinuous
direct image along `smallEtaleInclusion`. -/
instance forget_addCommGrpCat_preservesRightKanExtensions_smallEtaleInclusion
    (X : AlgebraicSpace S) :
    (forget AddCommGrpCat.{u}).PreservesRightKanExtensions (smallEtaleInclusion X).op :=
  sorry

/-- Continuous sheaf direct image commutes with postcomposition by a coefficient functor,
via the associator of precomposition and postcomposition. -/
def sheafPushforwardContinuousCompSheafComposeIso
    {C D : Type _} [Category C] [Category D] {A B : Type _} [Category A] [Category B]
    (u : C ⥤ D) (F : A ⥤ B) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [J.HasSheafCompose F] [K.HasSheafCompose F] :
    u.sheafPushforwardContinuous A J K ⋙ sheafCompose J F ≅
      sheafCompose K F ⋙ u.sheafPushforwardContinuous B J K :=
  NatIso.ofComponents
    (fun P ↦
      (fullyFaithfulSheafToPresheaf J B).preimageIso (Functor.associator u.op P.obj F))
    (fun {P Q} f ↦ sorry)

/-- Unfolding of `sheafPushforwardContinuousCompSheafComposeIso` on underlying presheaves. -/
theorem sheafPushforwardContinuousCompSheafComposeIso_sheafToPresheaf
    {C D : Type _} [Category C] [Category D] {A B : Type _} [Category A] [Category B]
    (u : C ⥤ D) (F : A ⥤ B) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [J.HasSheafCompose F] [K.HasSheafCompose F]
    (P : Sheaf K A) :
    (sheafToPresheaf J B).map
        ((sheafPushforwardContinuousCompSheafComposeIso u F J K).hom.app P) =
      (Functor.associator u.op P.obj F).hom :=
  sorry

/-- Forgetting abelian groups commutes with geometric direct image. -/
def addPushforwardForgetTypeIso {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    addPushforward a ⋙ forgetSpacesAddType Y ≅
      forgetSpacesAddType X ⋙ typePushforward a :=
  let uIncl := smallEtaleInclusion X
  let v := etaleBaseChange a
  let F := forget AddCommGrpCat.{u}
  let Ju := smallEtaleTopology X
  let Ku := spacesEtaleTopology X
  let Jv := smallEtaleTopology Y
  (Functor.associator
      (uIncl.sheafPushforwardCocontinuous AddCommGrpCat.{u} Ju Ku)
      (v.sheafPushforwardContinuous AddCommGrpCat.{u} Jv Ku)
      (sheafCompose Jv F)) ≪≫
    Functor.isoWhiskerLeft
      (uIncl.sheafPushforwardCocontinuous AddCommGrpCat.{u} Ju Ku)
      (sheafPushforwardContinuousCompSheafComposeIso v F Jv Ku) ≪≫
    (Functor.associator
        (uIncl.sheafPushforwardCocontinuous AddCommGrpCat.{u} Ju Ku)
        (sheafCompose Ku F)
        (v.sheafPushforwardContinuous (Type u) Jv Ku)).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafPushforwardCocontinuous.compSheafComposeIso uIncl F Ju Ku)
      (v.sheafPushforwardContinuous (Type u) Jv Ku) ≪≫
    Functor.associator
      (sheafCompose Ju F)
      (uIncl.sheafPushforwardCocontinuous (Type u) Ju Ku)
      (v.sheafPushforwardContinuous (Type u) Jv Ku)

/-- The forward comparison of `addPushforwardForgetTypeIso` is inverted by the reverse
comparison. -/
theorem addPushforwardForgetTypeIso_hom_comp_inv {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    (addPushforwardForgetTypeIso a).hom.app F ≫
      (addPushforwardForgetTypeIso a).inv.app F = 𝟙 _ :=
  sorry

/-- Additivity of a specified map between underlying type-valued sheaves. -/
def typeHomIsAdditive {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}}
    (f : (forgetSpacesAddType X).obj F ⟶ (forgetSpacesAddType X).obj G) : Prop :=
  ∀ U (x y : F.obj.obj U), ConcreteCategory.hom (f.hom.app U) (x + y) =
    @Add.add (G.obj.obj U) inferInstance
      (ConcreteCategory.hom (f.hom.app U) x) (ConcreteCategory.hom (f.hom.app U) y)

/-- Lift a type-valued sheaf map between additive sheaves to an additive sheaf map. -/
def addHomOfType {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}}
    (f : (forgetSpacesAddType X).obj F ⟶ (forgetSpacesAddType X).obj G)
    (hf : ∀ U (x y : F.obj.obj U),
      ConcreteCategory.hom (f.hom.app U) (x + y) =
        @Add.add (G.obj.obj U) inferInstance
          (ConcreteCategory.hom (f.hom.app U) x) (ConcreteCategory.hom (f.hom.app U) y)) :
    F ⟶ G :=
  { hom :=
      { app := fun U ↦
          AddCommGrpCat.ofHom
            (AddMonoidHom.mk'
              (fun x ↦ ConcreteCategory.hom (f.hom.app U) x) (hf U))
        naturality := fun _ _ _ ↦ sorry } }

/-- `addHomOfType` recovers the original type-valued map after forgetting additivity. -/
theorem addHomOfType_spec {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}}
    (f : (forgetSpacesAddType X).obj F ⟶ (forgetSpacesAddType X).obj G)
    (hf : ∀ U (x y : F.obj.obj U),
      ConcreteCategory.hom (f.hom.app U) (x + y) =
        @Add.add (G.obj.obj U) inferInstance
          (ConcreteCategory.hom (f.hom.app U) x) (ConcreteCategory.hom (f.hom.app U) y)) :
    (forgetSpacesAddType X).map (addHomOfType f hf) = f :=
  sorry

/-- The specified module direct-image comparison preserves addition sectionwise. -/
theorem modulePushforwardForgetAdd_add {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : X.Modules) :
    typeHomIsAdditive ((toSheafUnderlyingIso Y ((Modules.pushforward a).obj F)).hom ≫
      modulePushforwardForgetHom a F ≫
      (typePushforward a).map (toSheafUnderlyingIso X F).inv ≫
      (addPushforwardForgetTypeIso a).inv.app
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F)) := sorry

/-- Named additive comparison `toSheaf (a_* F) ⟶ a_* (toSheaf F)`, obtained from
`ModulePushforward.forgetIso` rather than a propositional sheaf equality. -/
def modulePushforwardForgetAdd {X Y : AlgebraicSpace S} (a : X ⟶ Y) (F : X.Modules) :
    (SheafOfModules.toSheaf (structureSheaf Y)).obj ((Modules.pushforward a).obj F) ⟶
      (addPushforward a).obj ((SheafOfModules.toSheaf (structureSheaf X)).obj F) :=
  addHomOfType (hf := modulePushforwardForgetAdd_add a F)
    ((toSheafUnderlyingIso Y ((Modules.pushforward a).obj F)).hom ≫
      modulePushforwardForgetHom a F ≫
      (typePushforward a).map (toSheafUnderlyingIso X F).inv ≫
      (addPushforwardForgetTypeIso a).inv.app
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F))

/-- Unfolding of `modulePushforwardForgetAdd`. -/
theorem modulePushforwardForgetAdd_eq {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : X.Modules) :
    modulePushforwardForgetAdd a F =
      addHomOfType (hf := modulePushforwardForgetAdd_add a F)
        ((toSheafUnderlyingIso Y ((Modules.pushforward a).obj F)).hom ≫
          modulePushforwardForgetHom a F ≫
          (typePushforward a).map (toSheafUnderlyingIso X F).inv ≫
          (addPushforwardForgetTypeIso a).inv.app
            ((SheafOfModules.toSheaf (structureSheaf X)).obj F)) :=
  rfl

/-- The adjunct of `D.d`, as an abelian sheaf map `a⁻¹ 𝒪_Y ⟶ C` on `X_étale`. -/
def derivationAdjunct {X Y B : AlgebraicSpace S} (sY : Y ⟶ B) (a : X ⟶ Y)
    {F : X.Modules} (D : derivations sY ((Modules.pushforward a).obj F)) :
    (addInverseImage a).obj
        ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
          (structureSheaf Y)) ⟶
      (SheafOfModules.toSheaf (structureSheaf X)).obj F :=
  pulledDerivation sY a D ≫
    (addInverseImage a).map (modulePushforwardForgetAdd a F) ≫
    (addInverseImageAdjunction a).counit.app
      ((SheafOfModules.toSheaf (structureSheaf X)).obj F)

/-- Unfolding of `derivationAdjunct`. -/
theorem derivationAdjunct_eq {X Y B : AlgebraicSpace S} (sY : Y ⟶ B) (a : X ⟶ Y)
    {F : X.Modules} (D : derivations sY ((Modules.pushforward a).obj F)) :
    derivationAdjunct sY a D =
      pulledDerivation sY a D ≫
        (addInverseImage a).map (modulePushforwardForgetAdd a F) ≫
        (addInverseImageAdjunction a).counit.app
          ((SheafOfModules.toSheaf (structureSheaf X)).obj F) :=
  rfl

/-- Geometric inverse image of the first-order inclusion `I/I² ⟶ 𝒪_{X'}`. -/
def conormalInverseImageIncl {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    ((ringedToposHom i).toTopos.moduleInverseImage (structureSheaf X')).obj
        (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)) ⟶
      ((ringedToposHom i).toTopos.moduleInverseImage (structureSheaf X')).obj
        (SheafOfModules.unit (structureSheaf X')) :=
  ((ringedToposHom i).toTopos.moduleInverseImage (structureSheaf X')).map
    (firstOrderIdealIncl i)

/-- Unfolding of `conormalInverseImageIncl`. -/
theorem conormalInverseImageIncl_eq {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    conormalInverseImageIncl i =
      ((ringedToposHom i).toTopos.moduleInverseImage (structureSheaf X')).map
        (firstOrderIdealIncl i) :=
  rfl

/-- Named comparison from the underlying sheaf of geometric module inverse image to
geometric inverse image of the underlying sheaf. -/
def moduleInverseImageForgetHom {Z X : AlgebraicSpace S} (j : Z ⟶ X) (F : X.Modules) :
    (ToInternal.underlying
          ((ringedToposHom j).toTopos.ringInverseImage.obj (structureSheaf X))).obj
        (((ringedToposHom j).toTopos.moduleInverseImage (structureSheaf X)).obj F) ⟶
      (ringedToposHom j).toTopos.inverseImage.obj
        ((ToInternal.underlying (structureSheaf X)).obj F) :=
  ((ringedToposHom j).toTopos.moduleInverseImageForgetIso (structureSheaf X)).hom.app F

/-- Unfolding of `moduleInverseImageForgetHom`. -/
theorem moduleInverseImageForgetHom_eq {Z X : AlgebraicSpace S} (j : Z ⟶ X)
    (F : X.Modules) :
    moduleInverseImageForgetHom j F =
      ((ringedToposHom j).toTopos.moduleInverseImageForgetIso
          (structureSheaf X)).hom.app F :=
  rfl

/-- Restriction of scalars along `j^♯` does not change the underlying type-valued sheaf. -/
def restrictScalarsUnderlyingIso {X Y : AlgebraicSpace S} (j : X ⟶ Y) (F : X.Modules) :
    (ToInternal.underlying (structureSheaf X)).obj F ≅
      (ToInternal.underlying
          ((ringedToposHom j).toTopos.ringInverseImage.obj (structureSheaf Y))).obj
        ((SheafOfModules.restrictScalars (ringedToposHom j).structureMap).obj F) :=
  Iso.refl _

/-- Unfolding of `restrictScalarsUnderlyingIso`. -/
theorem restrictScalarsUnderlyingIso_eq {X Y : AlgebraicSpace S} (j : X ⟶ Y)
    (F : X.Modules) :
    restrictScalarsUnderlyingIso j F =
      Iso.refl ((ToInternal.underlying (structureSheaf X)).obj F) :=
  rfl

/-- The unit `𝒪`-module and the underlying additive structure sheaf agree. -/
def unitToForgetAddIso (X : AlgebraicSpace S) :
    (SheafOfModules.toSheaf (structureSheaf X)).obj
        (SheafOfModules.unit (structureSheaf X)) ≅
      (sheafCompose (smallEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf X) where
  hom := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  inv := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Unfolding of the forward map of `unitToForgetAddIso`. -/
theorem unitToForgetAddIso_hom_eq (X : AlgebraicSpace S) :
    (unitToForgetAddIso X).hom =
      { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } } :=
  rfl

/-- The square comparing the coborder lift with the original closed immersion. -/
theorem coborderSquare {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsClosedImmersion i] :
    CommSq (𝟙 X) (IsImmersion.liftCoborder i) i (IsImmersion.coborderRange i).ι :=
  sorry

/-- Pull back the ambient quotient and restrict to the coborder definition of the conormal.
The equality transport is only the actual factorization of the morphism i. -/
def pullbackQuotientToConormal {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsClosedImmersion i] :
    (Modules.pullback i).obj
        (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)) ⟶
      Hom.conormalSheaf i :=
  (eqToIso (congrArg Modules.pullback (IsImmersion.liftCoborder_comp i).symm)).hom.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)) ≫
    (Modules.pullbackComp (IsImmersion.liftCoborder i) (IsImmersion.coborderRange i).ι).inv.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)) ≫
    (Modules.pullback (IsImmersion.liftCoborder i)).map
      (Hom.Conormal.idealQuotientMap (coborderSquare i))

/-- Restricting a closed immersion to its coborder preserves its conormal quotient. -/
instance pullbackQuotientToConormal_isIso {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsClosedImmersion i] : IsIso (pullbackQuotientToConormal i) := sorry

/-- The module-adjunction unit is invertible on the quotient annihilated by the ideal. -/
instance conormalQuotientUnit_isIso {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsClosedImmersion i] :
    IsIso ((Modules.pullbackPushforwardAdjunction i).unit.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i))) := sorry

/-- Supported quotient comparison using the inverse of the actual module-adjunction unit. -/
def pushforwardConormalToQuotient {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    (Modules.pushforward i).obj (Hom.conormalSheaf i) ⟶
      Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i) :=
  (Modules.pushforward i).map (inv (pullbackQuotientToConormal i)) ≫
    @inv _ _ _ _ ((Modules.pullbackPushforwardAdjunction i).unit.app
      (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)))
      (conormalQuotientUnit_isIso i)

/-- The specified module direct-image comparison preserves addition sectionwise. -/
theorem modulePushforwardForgetAddInv_add {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : X.Modules) :
    typeHomIsAdditive ((addPushforwardForgetTypeIso a).hom.app
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F) ≫
      (typePushforward a).map (toSheafUnderlyingIso X F).hom ≫
      (ModulePushforward.forgetIso (ringedToposHom a)).inv.app F ≫
      (toSheafUnderlyingIso Y ((Modules.pushforward a).obj F)).inv) := sorry

/-- Named additive comparison `i_* (toSheaf F) ⟶ toSheaf (i_* F)`, inverse to
`modulePushforwardForgetAdd`. -/
def modulePushforwardForgetAddInv {X Y : AlgebraicSpace S} (a : X ⟶ Y) (F : X.Modules) :
    (addPushforward a).obj ((SheafOfModules.toSheaf (structureSheaf X)).obj F) ⟶
      (SheafOfModules.toSheaf (structureSheaf Y)).obj ((Modules.pushforward a).obj F) :=
  addHomOfType (hf := modulePushforwardForgetAddInv_add a F)
    ((addPushforwardForgetTypeIso a).hom.app
        ((SheafOfModules.toSheaf (structureSheaf X)).obj F) ≫
      (typePushforward a).map (toSheafUnderlyingIso X F).hom ≫
      (ModulePushforward.forgetIso (ringedToposHom a)).inv.app F ≫
      (toSheafUnderlyingIso Y ((Modules.pushforward a).obj F)).inv)

/-- Unfolding of `modulePushforwardForgetAddInv`. -/
theorem modulePushforwardForgetAddInv_eq {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : X.Modules) :
    modulePushforwardForgetAddInv a F =
      addHomOfType (hf := modulePushforwardForgetAddInv_add a F)
        ((addPushforwardForgetTypeIso a).hom.app
            ((SheafOfModules.toSheaf (structureSheaf X)).obj F) ≫
          (typePushforward a).map (toSheafUnderlyingIso X F).hom ≫
          (ModulePushforward.forgetIso (ringedToposHom a)).inv.app F ≫
          (toSheafUnderlyingIso Y ((Modules.pushforward a).obj F)).inv) :=
  rfl

/-- The additive map `i_* C_{X/X'} ⟶ 𝒪_{X'}` obtained from `I/I² ⟶ 𝒪` after
identifying `i_* C` with `I/I²`. -/
def pushforwardConormalToStructure {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    (addPushforward i).obj
        ((SheafOfModules.toSheaf (structureSheaf X)).obj (Hom.conormalSheaf i)) ⟶
      (sheafCompose (smallEtaleTopology X') (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf X') :=
  modulePushforwardForgetAddInv i (Hom.conormalSheaf i) ≫
    (SheafOfModules.toSheaf (structureSheaf X')).map (pushforwardConormalToQuotient i) ≫
    (SheafOfModules.toSheaf (structureSheaf X')).map (firstOrderIdealIncl i) ≫
    (unitToForgetAddIso X').hom

/-- Unfolding of `pushforwardConormalToStructure`. -/
theorem pushforwardConormalToStructure_eq {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    pushforwardConormalToStructure i =
      modulePushforwardForgetAddInv i (Hom.conormalSheaf i) ≫
        (SheafOfModules.toSheaf (structureSheaf X')).map (pushforwardConormalToQuotient i) ≫
        (SheafOfModules.toSheaf (structureSheaf X')).map (firstOrderIdealIncl i) ≫
        (unitToForgetAddIso X').hom :=
  rfl

/-- Inverse-image form of `iY^♯` as abelian sheaves on `X_étale`. -/
def pulledRestrictionAdd {X Y Y' : AlgebraicSpace S} (a : X ⟶ Y) (iY : Y ⟶ Y') :
    (addInverseImage a).obj
        ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
          ((ringedToposHom iY).toTopos.ringInverseImage.obj (structureSheaf Y'))) ⟶
      (addInverseImage a).obj
        ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
          (structureSheaf Y)) :=
  (addInverseImage a).map
    ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).map
      (ringedToposHom iY).structureMap)

/-- Unfolding of `pulledRestrictionAdd`. -/
theorem pulledRestrictionAdd_eq {X Y Y' : AlgebraicSpace S} (a : X ⟶ Y) (iY : Y ⟶ Y') :
    pulledRestrictionAdd a iY =
      (addInverseImage a).map
        ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).map
          (ringedToposHom iY).structureMap) :=
  rfl

/-- Restriction of additive sheaves commutes with forgetting ring structure. -/
def restrictForgetRingIso (X : AlgebraicSpace S)
    (F : Sheaf (spacesEtaleTopology X) RingCat.{u}) :
    (restrictSpacesAdd X).obj ((forgetSpacesRing X).obj F) ≅
      (sheafCompose (smallEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (((smallEtaleInclusion X).sheafPushforwardContinuous RingCat.{u}
            (smallEtaleTopology X) (spacesEtaleTopology X)).obj F) :=
  (sheafPushforwardContinuousCompSheafComposeIso
      (smallEtaleInclusion X) (forget₂ RingCat AddCommGrpCat.{u})
      (smallEtaleTopology X) (spacesEtaleTopology X)).symm.app F

/-- Unfolding of `restrictForgetRingIso`. -/
theorem restrictForgetRingIso_eq (X : AlgebraicSpace S)
    (F : Sheaf (spacesEtaleTopology X) RingCat.{u}) :
    restrictForgetRingIso X F =
      (sheafPushforwardContinuousCompSheafComposeIso
          (smallEtaleInclusion X) (forget₂ RingCat AddCommGrpCat.{u})
          (smallEtaleTopology X) (spacesEtaleTopology X)).symm.app F :=
  rfl

/-- The dense small étale inclusion induces an equivalence on type-valued sheaves. -/
theorem smallEtaleTypeRestriction_isEquivalence (X : AlgebraicSpace S) :
    ((smallEtaleInclusion X).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X)).IsEquivalence := sorry

/-- Type-valued restriction from spaces to the dense small étale subsite. -/
abbrev restrictSpacesType (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) (Type u) ⥤ Sheaf (smallEtaleTopology X) (Type u) :=
  (smallEtaleInclusion X).sheafPushforwardContinuous (Type u)
    (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Restriction to the small étale subsite is an equivalence on sheaves. -/
instance restrictSpacesType_isEquivalence (X : AlgebraicSpace S) :
    (restrictSpacesType X).IsEquivalence := smallEtaleTypeRestriction_isEquivalence X

/-- The dense-subsite equivalence with its specified right Kan extension. -/
def smallSpacesEquivalence (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) (Type u) ≌ Sheaf (smallEtaleTopology X) (Type u) :=
  ((smallEtaleInclusion X).sheafAdjunctionCocontinuous (Type u)
    (smallEtaleTopology X) (spacesEtaleTopology X)).toEquivalence

/-- Direct-image comparison induced by the actual base-change square of site functors. -/
def smallSpacesPushforwardIso {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    (morphismOfTopoi a).pushforward ≅
      (smallSpacesEquivalence X).inverse ⋙
        (spacesRingedToposHom a).toTopos.pushforward ⋙
          (smallSpacesEquivalence Y).functor :=
  Functor.isoWhiskerLeft (smallSpacesEquivalence X).inverse
    (Functor.sheafPushforwardContinuousComp'
      (smallEtaleInclusion_comp_spacesEtalePullback a) (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y) (spacesEtaleTopology X)).symm

/-- The inverse-image mate of the specified direct-image comparison. -/
def smallSpacesInverseIso {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    (smallSpacesEquivalence Y).inverse ⋙
        (spacesRingedToposHom a).toTopos.inverseImage ⋙
          (smallSpacesEquivalence X).functor ≅ (morphismOfTopoi a).inverseImage :=
  Adjunction.leftAdjointUniq
    ((((smallSpacesEquivalence Y).symm.toAdjunction.comp
      (spacesRingedToposHom a).toTopos.adjunction).comp
        (smallSpacesEquivalence X).toAdjunction).ofNatIsoRight
          (smallSpacesPushforwardIso a).symm)
    (morphismOfTopoi a).adjunction

/-- Inverse image commutes with the underlying type of an additive sheaf:
the map is the adjunction mate of the additive unit and the direct-image comparison. -/
def inverseImageForgetAddHom {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    (morphismOfTopoi a).inverseImage.obj ((forgetSpacesAddType Y).obj F) ⟶
      (forgetSpacesAddType X).obj ((addInverseImage a).obj F) :=
  ((morphismOfTopoi a).adjunction.homEquiv _ _).symm
    ((forgetSpacesAddType Y).map ((addInverseImageAdjunction a).unit.app F) ≫
      (addPushforwardForgetTypeIso a).hom.app ((addInverseImage a).obj F))

/-- The canonical additive forgetful inverse-image mate is invertible. -/
instance inverseImageForgetAddHom_isIso {X Y : AlgebraicSpace S} (a : X ⟶ Y)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u}) :
    IsIso (inverseImageForgetAddHom a F) := sorry

/-- The underlying comparison for the inverse image of the structure sheaf,
composed from ring forgetting, dense-subsite Kan extension, and adjunction mates. -/
def restrictInverseImageTypeHom {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    (forgetSpacesAddType X).obj ((restrictSpacesAdd X).obj
      ((forgetSpacesRing X).obj ((spacesRingedToposHom a).toTopos.ringInverseImage.obj
        (spacesStructureSheaf Y)))) ⟶
    (forgetSpacesAddType X).obj ((addInverseImage a).obj
      ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf Y))) :=
  (restrictSpacesType X).map
      ((spacesRingedToposHom a).toTopos.ringInverseImageForgetIso.hom.app
        (spacesStructureSheaf Y)) ≫
    (restrictSpacesType X).map ((spacesRingedToposHom a).toTopos.inverseImage.map
      ((Functor.sheafPushforwardCocontinuous.compSheafComposeIso
        (smallEtaleInclusion Y) (forget RingCat.{u})
        (smallEtaleTopology Y) (spacesEtaleTopology Y)).hom.app (structureSheaf Y))) ≫
    (smallSpacesInverseIso a).hom.app
      ((sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj (structureSheaf Y)) ≫
    inverseImageForgetAddHom a
      ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf Y))

/-- Each factor in the structure-sheaf inverse-image comparison is invertible. -/
instance restrictInverseImageTypeHom_isIso {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    IsIso (restrictInverseImageTypeHom a) := sorry

/-- The small-versus-spaces comparison, with underlying maps fixed by adjunction mates. -/
def restrictInverseImageIso {X Y : AlgebraicSpace S} (a : X ⟶ Y) :
    (restrictSpacesAdd X).obj
        ((forgetSpacesRing X).obj
          ((spacesRingedToposHom a).toTopos.ringInverseImage.obj
            (spacesStructureSheaf Y))) ≅
      (addInverseImage a).obj
        ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
          (structureSheaf Y)) where
  hom := addHomOfType (restrictInverseImageTypeHom a) (hf := sorry)
  inv := addHomOfType (inv (restrictInverseImageTypeHom a)) (hf := sorry)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The inverse-image/direct-image counit is invertible on a thickening. -/
instance thickeningCounit_isIso {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsFirstOrderThickening i]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    IsIso ((addInverseImageAdjunction i).counit.app F) := sorry

/-- The comparison `F ⟶ i^{-1} i_* F` on a first-order thickening. -/
def toInverseImagePushforward {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    F ⟶ (addInverseImage i).obj ((addPushforward i).obj F) :=
  @inv _ _ _ _ ((addInverseImageAdjunction i).counit.app F) (thickeningCounit_isIso i F)

/-- Unfolding of `toInverseImagePushforward`. -/
theorem toInverseImagePushforward_eq {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    toInverseImagePushforward i F =
      @inv _ _ _ _ ((addInverseImageAdjunction i).counit.app F) (thickeningCounit_isIso i F) :=
  rfl

/-- The inclusion `C_{X/X'} ⟶ i^{-1} 𝒪_{X'}` of a first-order thickening, obtained
as the geometric inverse image of `I/I² ⟶ 𝒪` after the forgetful comparison
`i_* C ⟶ I/I²` that does not extend scalars. -/
def conormalInclusion {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    (SheafOfModules.toSheaf (structureSheaf X)).obj (Hom.conormalSheaf i) ⟶
      (restrictSpacesAdd X).obj ((forgetSpacesRing X).obj (closedStructureSheaf i)) :=
  toInverseImagePushforward i
      ((SheafOfModules.toSheaf (structureSheaf X)).obj (Hom.conormalSheaf i)) ≫
    (addInverseImage i).map (pushforwardConormalToStructure i) ≫
    (restrictInverseImageIso i).inv

/-- Unfolding of `conormalInclusion`. -/
theorem conormalInclusion_eq {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    conormalInclusion i =
      toInverseImagePushforward i
          ((SheafOfModules.toSheaf (structureSheaf X)).obj (Hom.conormalSheaf i)) ≫
        (addInverseImage i).map (pushforwardConormalToStructure i) ≫
        (restrictInverseImageIso i).inv :=
  rfl

/-- The source composite `𝒪_{Y'} ⟶ 𝒪_Y ⟶^D a_* C_{X/X'} ⟶ a_* 𝒪_{X'}`,
transported to the hom-type of `structureMapDifference_restrict`. -/
def factorizationMap {X X' Y Y' B : AlgebraicSpace S} (sY : Y ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX]
    (D : derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX))) :
    (restrictSpacesAdd X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY)) ⟶
      (restrictSpacesAdd X).obj ((forgetSpacesRing X).obj (closedStructureSheaf iX)) :=
  pulledRestriction a iY ≫
    (restrictInverseImageIso a).hom ≫
    derivationAdjunct sY a D ≫
    conormalInclusion iX

/-- Unfolding of `factorizationMap`. -/
theorem factorizationMap_eq {X X' Y Y' B : AlgebraicSpace S} (sY : Y ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX]
    (D : derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX))) :
    factorizationMap sY iX iY a D =
      pulledRestriction a iY ≫
        (restrictInverseImageIso a).hom ≫
        derivationAdjunct sY a D ≫
        conormalInclusion iX :=
  rfl

/-- Sectionwise values of the transported composite through `D.d` and
`conormalInclusion`. -/
def factorizationMap_apply {X X' Y Y' B : AlgebraicSpace S} (sY : Y ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX]
    (D : derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX)))
    (V : (smallEtaleSite X)ᵒᵖ)
    (x : ((restrictSpacesAdd X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY))).obj.obj V) :
    ((restrictSpacesAdd X).obj
        ((forgetSpacesRing X).obj (closedStructureSheaf iX))).obj.obj V :=
  ConcreteCategory.hom ((factorizationMap sY iX iY a D).hom.app V) x

/-- Unfolding of `factorizationMap_apply`. -/
theorem factorizationMap_apply_eq {X X' Y Y' B : AlgebraicSpace S} (sY : Y ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX]
    (D : derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX)))
    (V : (smallEtaleSite X)ᵒᵖ)
    (x : ((restrictSpacesAdd X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY))).obj.obj V) :
    factorizationMap_apply sY iX iY a D V x =
      ConcreteCategory.hom ((factorizationMap sY iX iY a D).hom.app V) x :=
  rfl

/-- Two morphisms of first-order thickenings over `B` with a common reduced map and
equal Lemma 76.5.3 conormal maps differ by an `𝒪_B`-derivation
`𝒪_Y ⟶ a_* C_{X/X'}`. -/
theorem exists_differenceDerivation {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
    (ha' : a' ≫ sY' = sX') (hb' : b' ≫ sY' = sX')
    (sqA : CommSq a iX iY a') (sqB : CommSq a iX iY b')
    (hconormal : Hom.Conormal.map sqA = Hom.Conormal.map sqB) :
    ∃ D : derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX)),
      structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm =
        factorizationMap sY iX iY a D :=
  sorry

/-- A witness derivation recovers the inverse-image difference of `(a')^♯` and
`(b')^♯` as the composite through `D.d` and `conormalInclusion`. -/
theorem exists_differenceDerivation_spec {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
    (ha' : a' ≫ sY' = sX') (hb' : b' ≫ sY' = sX')
    (sqA : CommSq a iX iY a') (sqB : CommSq a iX iY b')
    (hconormal : Hom.Conormal.map sqA = Hom.Conormal.map sqB)
    (D : derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX)))
    (hD : structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm =
      factorizationMap sY iX iY a D)
    (V : (smallEtaleSite X)ᵒᵖ)
    (x : ((restrictSpacesAdd X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY))).obj.obj V) :
    ConcreteCategory.hom
        ((structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm).hom.app V) x =
      ConcreteCategory.hom ((conormalInclusion iX).hom.app V)
        (ConcreteCategory.hom ((derivationAdjunct sY a D).hom.app V)
          (ConcreteCategory.hom ((restrictInverseImageIso a).hom.hom.app V)
            (ConcreteCategory.hom ((pulledRestriction a iY).hom.app V) x))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
