module

public import stacks_project.Chap96.Proposition_96_14_3_Comparison
public import stacks_project.Chap96.Proposition_96_14_3_Functor
public import stacks_project.Chap96.Proposition_96_14_3_Inverse
public import stacks_project.Chap66.Lemma_66_27_3_Space
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-coherent modules on a quotient stack

For a groupoid in algebraic spaces `(U, R, s, t, c)` over `S`, with quotient
stack `𝒳 = [U / R]`, the category of quasi-coherent modules on `𝒳` is equivalent
to the category of quasi-coherent modules on the groupoid.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.ObjectProperty
open CategoryTheory.Sheaf.InternalModule
open CategoryTheory.Functor
open FiberedCategoryOver.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- The category fibred in groupoids associated to the object space of `G`. -/
def objectGroupoids : GroupoidsOver S :=
  (G.U.left).toGroupoids

/-- `objectGroupoids` is `toGroupoids` of the object space of `G`. -/
theorem objectGroupoids_eq : objectGroupoids G = (G.U.left).toGroupoids :=
  rfl

/-- Restriction after pullback along `toGroupoids.map (pointHom x)` compares with
small-étale pullback along `pointHom x`. -/
def restrict_pointHomPullbackIso (x : G.preQuotient.total) :
    pullback (AlgebraicSpace.toGroupoids.map (pointHom G x)) ⋙
      restrict (idSpace (ofOver x.base)) ≅
      restrict (idSpace G.U.left) ⋙ AlgebraicSpace.QCoh.pullback (pointHom G x) :=
  restrict_pullbackIso (idSpace (ofOver x.base)) (idSpace G.U.left)
      (AlgebraicSpace.toGroupoids.map (pointHom G x))
      (recoveredIdMapTwoCell (pointHom G x)) ≪≫
    Functor.isoWhiskerLeft (restrict (idSpace G.U.left))
      (GroupoidAlgebraicSpace.pullbackEqIso (recoveredIdMap_eq (pointHom G x)))

/-- `u_small^* A` identifies with restriction to `T` of the pullback of `π_U^* A`
along `𝒮_T ⟶ 𝒮_U`. -/
def pulledObj_piStarIso (A : G.QCoh) (x : G.preQuotient.total) :
    pulledObj G A x ≅
      (restrict (idSpace (ofOver x.base))).obj
        ((pullback (AlgebraicSpace.toGroupoids.map (pointHom G x))).obj
          ((piStar (idSpace G.U.left)).obj A.obj)) :=
  (AlgebraicSpace.QCoh.pullback (pointHom G x)).mapIso
      ((restrict_piStarIso (idSpace G.U.left)).app A.obj) ≪≫
    (restrict_pointHomPullbackIso G x).symm.app
      ((piStar (idSpace G.U.left)).obj A.obj)

/-- Global sections of `u_small^* A` identify with global sections of the restricted
pullback of `π_U^* A`. -/
def gammaObj_piStarRestrictIso (A : G.QCoh) (x : G.preQuotient.total) :
    gammaObj G A x ≅
      (RingedSpace.moduleGlobalSectionsFunctor (x.base.left).toRingedSpace).obj
        ((AlgebraicSpace.Modules.restrictToScheme x.base).obj
          ((restrict (idSpace (ofOver x.base))).obj
            ((pullback (AlgebraicSpace.toGroupoids.map (pointHom G x))).obj
              ((piStar (idSpace G.U.left)).obj A.obj))).obj) :=
  (RingedSpace.moduleGlobalSectionsFunctor (x.base.left).toRingedSpace).mapIso
    ((AlgebraicSpace.Modules.restrictToScheme x.base).mapIso
      ((AlgebraicSpace.QCoh.inclusion (ofOver x.base)).mapIso (pulledObj_piStarIso G A x)))

/-- The image of the terminal open of `T` under the small étale-to-opens site
morphism, as an étale object of the underlying scheme. -/
abbrev schemeTopEtale (T : Over S) : T.left.Etale :=
  (smallEtaleToOpensRingedHom T.left).base.obj ⊤

/-- `schemeTopEtale` is the base image of the terminal open. -/
theorem schemeTopEtale_eq (T : Over S) :
    schemeTopEtale T = (smallEtaleToOpensRingedHom T.left).base.obj ⊤ :=
  rfl

/-- The identity étale object of `ofOver T` is the image of `schemeTopEtale`
under `schemeEtaleRingedHom`. -/
theorem schemeEtaleRingedHom_base_top (T : Over S) :
    (schemeEtaleRingedHom T).base.obj (schemeTopEtale T) =
      AlgebraicSpace.smallEtaleSite.id T :=
  sorry

/-- The object of `[U /ₚ R]` obtained by applying the object inclusion to an object of
`𝒮_U`. -/
def atlasToPreQuotientObj (y : (objectGroupoids G).total) : G.preQuotient.total :=
  (toCartesianBasedFunctor G.atlasToPreQuotient).toFunctor.obj y

/-- `atlasToPreQuotientObj` is the cartesian total functor of the object inclusion. -/
theorem atlasToPreQuotientObj_eq (y : (objectGroupoids G).total) :
    atlasToPreQuotientObj G y =
      (toCartesianBasedFunctor G.atlasToPreQuotient).toFunctor.obj y :=
  rfl

/-- The object of `𝒮_U` with the same scheme and `U`-point as an object of `[U /ₚ R]`. -/
def objectPoint (x : G.preQuotient.total) : (objectGroupoids G).total :=
  Opposite.op ⟨Opposite.op x.base, x.fiber⟩

/-- Object-inclusion of `objectPoint x` recovers `x`. -/
theorem atlasToPreQuotient_objectPoint (x : G.preQuotient.total) :
    atlasToPreQuotientObj G (objectPoint G x) = x :=
  sorry

/-- The object-inclusion of an object of `𝒮_U` recovers that object from its
prequotient image. -/
theorem objectPoint_atlasToPreQuotient (y : (objectGroupoids G).total) :
    objectPoint G (atlasToPreQuotientObj G y) = y :=
  sorry

/-- Atlas image of `objectPoint x` recovers stackification of `x`. -/
theorem atlas_objectPoint (x : G.preQuotient.total) :
    (toFunctor G.atlas).obj (objectPoint G x) =
      (toFunctor G.stackificationHom).obj x :=
  sorry

/-- Underlying sheaf of quasi-coherent pullback along the object inclusion. -/
def pullback_fromPreQuotient_compιIso (A : G.QCoh) :
    ((pullback G.atlasToPreQuotient).obj ((fromPreQuotient G).obj A)).obj ≅
      (modulePullback G.atlasToPreQuotient).obj ((fromPreQuotient G).obj A).obj :=
  (FullSubcategory.restrict.compιIso (modulePullback G.atlasToPreQuotient)
      (modulePullback_le_inverseImage G.atlasToPreQuotient)).app
    ((fromPreQuotient G).obj A)

/-- `pullback_fromPreQuotient_compιIso` is the inclusion comparison of
`QCoh.pullback`. -/
theorem pullback_fromPreQuotient_compιIso_eq (A : G.QCoh) :
    pullback_fromPreQuotient_compιIso G A =
      (FullSubcategory.restrict.compιIso (modulePullback G.atlasToPreQuotient)
          (modulePullback_le_inverseImage G.atlasToPreQuotient)).app
        ((fromPreQuotient G).obj A) :=
  rfl

/-- The coefficient isomorphism of `structureSheafMap f` at an object of `X`. -/
def structureSheafMap_appIso {X Y : GroupoidsOver S} (f : X ⟶ Y) (x : X.totalᵒᵖ) :
    (structureSheaf X).obj.obj x ≅ (inverseImageStructureSheaf f).obj.obj x :=
  ((sheafToPresheaf (inheritedFppfTopology X) RingCat.{u}).mapIso
      (structureSheafIso f).symm).app x

/-- `structureSheafMap_appIso` is the presheaf component of `structureSheafIso`. -/
theorem structureSheafMap_appIso_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (x : X.totalᵒᵖ) :
    structureSheafMap_appIso f x =
      ((sheafToPresheaf (inheritedFppfTopology X) RingCat.{u}).mapIso
          (structureSheafIso f).symm).app x :=
  rfl

/-- The ring equivalence underlying `structureSheafMap_appIso`. -/
def structureSheafMap_appRingEquiv {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (x : X.totalᵒᵖ) :
    (structureSheaf X).obj.obj x ≃+* (inverseImageStructureSheaf f).obj.obj x :=
  RingEquiv.ofRingHom
    (structureSheafMap_appIso f x).hom.hom
    (structureSheafMap_appIso f x).inv.hom
    sorry sorry

/-- Transport a morphism after restriction of scalars along a ring equivalence
back to the original coefficient ring. -/
def restrictScalars_reflect {R S : RingCat.{u}} (e : R ≃+* S)
    {M N : ModuleCat.{u} S}
    (g : (ModuleCat.restrictScalars e.toRingHom).obj M ⟶
      (ModuleCat.restrictScalars e.toRingHom).obj N) :
    M ⟶ N :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).unitIso.hom.app M ≫
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).inverse.map g ≫
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).unitIso.inv.app N

/-- Evaluation of module inverse image along `f` is restriction of scalars of
evaluation at the cartesian image object. -/
theorem modulePullback_eval_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheaf Y)) (x : X.total) :
    ((modulePullback f).obj F).val.obj (op x) =
      (ModuleCat.restrictScalars
          ((structureSheafMap f).hom.app (op x)).hom).obj
        (F.val.obj (op ((toCartesianBasedFunctor f).toFunctor.obj x))) :=
  sorry

/-- Evaluation of module inverse image along `f` is restriction of scalars of
evaluation at the cartesian image object. -/
def modulePullback_evalIso {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheaf Y)) (x : X.total) :
    ((modulePullback f).obj F).val.obj (op x) ≅
      (ModuleCat.restrictScalars
          ((structureSheafMap f).hom.app (op x)).hom).obj
        (F.val.obj (op ((toCartesianBasedFunctor f).toFunctor.obj x))) :=
  eqToIso (modulePullback_eval_eq f F x)

/-- `modulePullback_evalIso` is the pushforward unfolding of `modulePullback`. -/
theorem modulePullback_evalIso_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheaf Y)) (x : X.total) :
    modulePullback_evalIso f F x = eqToIso (modulePullback_eval_eq f F x) :=
  rfl

/-- Underlying sheaf of `QCoh.pullback f` compared with `modulePullback f`. -/
def pullback_compιIso {X Y : GroupoidsOver S} (f : X ⟶ Y) (F : QCoh Y) :
    ((pullback f).obj F).obj ≅ (modulePullback f).obj F.obj :=
  (FullSubcategory.restrict.compιIso (modulePullback f)
      (modulePullback_le_inverseImage f)).app F

/-- `pullback_compιIso` is the inclusion comparison of `QCoh.pullback`. -/
theorem pullback_compιIso_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) (F : QCoh Y) :
    pullback_compιIso f F =
      (FullSubcategory.restrict.compιIso (modulePullback f)
          (modulePullback_le_inverseImage f)).app F :=
  rfl

/-- Object-equality transport of a prequotient module sheaf along
`atlasToPreQuotient_objectPoint`. -/
def fromPreQuotient_objectPoint_eqToHom (A : G.QCoh) (x : G.preQuotient.total) :
    ((fromPreQuotient G).obj A).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x))) ⟶
      ((fromPreQuotient G).obj A).obj.val.obj (op x) :=
  ((fromPreQuotient G).obj A).obj.val.map
    (eqToHom (congrArg Opposite.op (atlasToPreQuotient_objectPoint G x)))

/-- Inverse object-equality transport of a prequotient module sheaf along
`atlasToPreQuotient_objectPoint`. -/
def fromPreQuotient_objectPoint_eqToHom_inv (A : G.QCoh)
    (x : G.preQuotient.total) :
    ((fromPreQuotient G).obj A).obj.val.obj (op x) ⟶
      ((fromPreQuotient G).obj A).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x))) :=
  ((fromPreQuotient G).obj A).obj.val.map
    (eqToHom (congrArg Opposite.op (atlasToPreQuotient_objectPoint G x).symm))

/-- Object-equality transport of stackification pullback along
`atlasToPreQuotient_objectPoint`. -/
def stackification_objectPoint_eqToHom (F : QCoh G.quotientStack)
    (x : G.preQuotient.total) :
    ((pullback G.stackificationHom).obj F).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x))) ⟶
      ((pullback G.stackificationHom).obj F).obj.val.obj (op x) :=
  ((pullback G.stackificationHom).obj F).obj.val.map
    (eqToHom (congrArg Opposite.op (atlasToPreQuotient_objectPoint G x)))

/-- Inverse object-equality transport of stackification pullback along
`atlasToPreQuotient_objectPoint`. -/
def stackification_objectPoint_eqToHom_inv (F : QCoh G.quotientStack)
    (x : G.preQuotient.total) :
    ((pullback G.stackificationHom).obj F).obj.val.obj (op x) ⟶
      ((pullback G.stackificationHom).obj F).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x))) :=
  ((pullback G.stackificationHom).obj F).obj.val.map
    (eqToHom (congrArg Opposite.op (atlasToPreQuotient_objectPoint G x).symm))

/-- Unfolding of Zariski global sections of `restrictToScheme` as restriction of
scalars of the étale-to-opens pushforward, evaluated at the terminal open. -/
def schemeGamma_opensEvalIso (T : Over S) (M : (ofOver T).Modules) :
    (RingedSpace.moduleGlobalSectionsFunctor T.left.toRingedSpace).obj
      ((AlgebraicSpace.Modules.restrictToScheme T).obj M) ≅
      (ModuleCat.restrictScalars
          ((opensStructureToRingCatSheaf T.left).hom.app (op ⊤)).hom).obj
        (((smallEtaleToOpensRingedHom T.left).modulePushforward.{u}.obj
          ((schemeEtaleRingedHom T).modulePushforward.{u}.obj
            ((AlgebraicSpace.Modules.restrictFunctor (𝟙 (ofOver T))).obj
              M))).val.obj (op ⊤)) :=
  Iso.refl _

/-- `schemeGamma_opensEvalIso` is the definitional unfolding of
`restrictToScheme`. -/
theorem schemeGamma_opensEvalIso_eq (T : Over S) (M : (ofOver T).Modules) :
    schemeGamma_opensEvalIso T M = Iso.refl _ :=
  rfl

/-- Evaluation of `smallEtaleToOpensRingedHom.modulePushforward` at the terminal
open is restriction of scalars of evaluation at `schemeTopEtale`. -/
theorem smallEtaleToOpens_eval_eq (T : Over S)
    (N : SheafOfModules.{u} (Small.ringedSite T.left).structureSheaf) :
    ((smallEtaleToOpensRingedHom T.left).modulePushforward.{u}.obj N).val.obj
        (op ⊤) =
      (ModuleCat.restrictScalars
          ((smallEtaleToOpensRingedHom T.left).structureSheafMap.hom.app
            (op ⊤)).hom).obj
        (N.val.obj (op (schemeTopEtale T))) :=
  sorry

/-- The identity étale object of `T` used by `schemeEtaleRingedHom` at the
terminal open. -/
abbrev schemeEtaleTop (T : Over S) : AlgebraicSpace.smallEtaleSite (ofOver T) :=
  (schemeEtaleRingedHom T).base.obj (schemeTopEtale T)

/-- `schemeEtaleTop` is the base image of `schemeTopEtale`. -/
theorem schemeEtaleTop_eq (T : Over S) :
    schemeEtaleTop T = (schemeEtaleRingedHom T).base.obj (schemeTopEtale T) :=
  rfl

/-- Evaluation of `schemeEtaleRingedHom.modulePushforward` at `schemeTopEtale` is
restriction of scalars of evaluation at `schemeEtaleTop`. -/
theorem schemeEtale_eval_eq (T : Over S) (M : (ofOver T).Modules) :
    ((schemeEtaleRingedHom T).modulePushforward.{u}.obj
          ((AlgebraicSpace.Modules.restrictFunctor (𝟙 (ofOver T))).obj M)).val.obj
        (op (schemeTopEtale T)) =
      (ModuleCat.restrictScalars
          ((schemeEtaleRingedHom T).structureSheafMap.hom.app
            (op (schemeTopEtale T))).hom).obj
        (M.val.obj (op (schemeEtaleTop T))) :=
  sorry

/-- Zariski global sections of `restrictToScheme` identify with evaluation at
`schemeEtaleTop` after restriction of scalars along the structure-sheaf maps
of `smallEtaleToOpensRingedHom` and `schemeEtaleRingedHom`. -/
def schemeGamma_idEvalIso (T : Over S) (M : (ofOver T).Modules) :
    (RingedSpace.moduleGlobalSectionsFunctor T.left.toRingedSpace).obj
      ((AlgebraicSpace.Modules.restrictToScheme T).obj M) ≅
      (ModuleCat.restrictScalars
          ((opensStructureToRingCatSheaf T.left).hom.app (op ⊤)).hom).obj
        ((ModuleCat.restrictScalars
            ((smallEtaleToOpensRingedHom T.left).structureSheafMap.hom.app
              (op ⊤)).hom).obj
          ((ModuleCat.restrictScalars
              ((schemeEtaleRingedHom T).structureSheafMap.hom.app
                (op (schemeTopEtale T))).hom).obj
            (M.val.obj (op (schemeEtaleTop T))))) :=
  schemeGamma_opensEvalIso T M ≪≫
    eqToIso (congrArg
        (fun N ↦
          (ModuleCat.restrictScalars
              ((opensStructureToRingCatSheaf T.left).hom.app (op ⊤)).hom).obj N)
        (smallEtaleToOpens_eval_eq T
          ((schemeEtaleRingedHom T).modulePushforward.{u}.obj
            ((AlgebraicSpace.Modules.restrictFunctor (𝟙 (ofOver T))).obj M)))) ≪≫
    (ModuleCat.restrictScalars
        ((opensStructureToRingCatSheaf T.left).hom.app (op ⊤)).hom).mapIso
      ((ModuleCat.restrictScalars
          ((smallEtaleToOpensRingedHom T.left).structureSheafMap.hom.app
            (op ⊤)).hom).mapIso
        (eqToIso (schemeEtale_eval_eq T M)))

/-- `schemeGamma_idEvalIso` is the composite of the `restrictToScheme` unfolding
with the two ringed-site evaluation identifications. -/
theorem schemeGamma_idEvalIso_eq (T : Over S) (M : (ofOver T).Modules) :
    schemeGamma_idEvalIso T M =
      schemeGamma_opensEvalIso T M ≪≫
        eqToIso (congrArg
            (fun N ↦
              (ModuleCat.restrictScalars
                  ((opensStructureToRingCatSheaf T.left).hom.app (op ⊤)).hom).obj N)
            (smallEtaleToOpens_eval_eq T
              ((schemeEtaleRingedHom T).modulePushforward.{u}.obj
                ((AlgebraicSpace.Modules.restrictFunctor (𝟙 (ofOver T))).obj M)))) ≪≫
        (ModuleCat.restrictScalars
            ((opensStructureToRingCatSheaf T.left).hom.app (op ⊤)).hom).mapIso
          ((ModuleCat.restrictScalars
              ((smallEtaleToOpensRingedHom T.left).structureSheafMap.hom.app
                (op ⊤)).hom).mapIso
            (eqToIso (schemeEtale_eval_eq T M))) :=
  rfl

/-- Global sections of `u_small^* A` identify with nested restriction of scalars
of evaluation of that pullback at `schemeEtaleTop`. -/
def gammaObj_idEvalIso (A : G.QCoh) (x : G.preQuotient.total) :
    gammaObj G A x ≅
      (ModuleCat.restrictScalars
          ((opensStructureToRingCatSheaf x.base.left).hom.app (op ⊤)).hom).obj
        ((ModuleCat.restrictScalars
            ((smallEtaleToOpensRingedHom x.base.left).structureSheafMap.hom.app
              (op ⊤)).hom).obj
          ((ModuleCat.restrictScalars
              ((schemeEtaleRingedHom x.base).structureSheafMap.hom.app
                (op (schemeTopEtale x.base))).hom).obj
            ((pulledObj G A x).obj.val.obj (op (schemeEtaleTop x.base))))) :=
  schemeGamma_idEvalIso x.base (pulledObj G A x).obj

/-- `gammaObj_idEvalIso` is `schemeGamma_idEvalIso` of `pulledObj`. -/
theorem gammaObj_idEvalIso_eq (A : G.QCoh) (x : G.preQuotient.total) :
    gammaObj_idEvalIso G A x =
      schemeGamma_idEvalIso x.base (pulledObj G A x).obj :=
  rfl

/-- The `ofOver T`-module obtained by restricting the pullback of `π_U^* A`
along `𝒮_T ⟶ 𝒮_U`. -/
def piStarPulledModules (A : G.QCoh) (x : G.preQuotient.total) :
    (ofOver x.base).Modules :=
  ((restrict (idSpace (ofOver x.base))).obj
    ((pullback (AlgebraicSpace.toGroupoids.map (pointHom G x))).obj
      ((piStar (idSpace G.U.left)).obj A.obj))).obj

/-- `piStarPulledModules` is restriction of the pullback of `π_U^* A`. -/
theorem piStarPulledModules_eq (A : G.QCoh) (x : G.preQuotient.total) :
    piStarPulledModules G A x =
      ((restrict (idSpace (ofOver x.base))).obj
        ((pullback (AlgebraicSpace.toGroupoids.map (pointHom G x))).obj
          ((piStar (idSpace G.U.left)).obj A.obj))).obj :=
  rfl

/-- Site comparison of Zariski global sections of the restricted pullback of
`π_U^* A` with nested restriction of scalars of evaluation at
`schemeEtaleTop`. -/
def piStarPulled_idEvalIso (A : G.QCoh) (x : G.preQuotient.total) :=
  schemeGamma_idEvalIso x.base (piStarPulledModules G A x)

/-- `piStarPulled_idEvalIso` is `schemeGamma_idEvalIso` of
`piStarPulledModules`. -/
theorem piStarPulled_idEvalIso_eq (A : G.QCoh) (x : G.preQuotient.total) :
    piStarPulled_idEvalIso G A x =
      schemeGamma_idEvalIso x.base (piStarPulledModules G A x) :=
  rfl

/-- Inclusion comparison of object-inclusion pullback of the Γ-sheaf, evaluated
at an object of `𝒮_U`. -/
def pullback_fromPreQuotient_evalIso (A : G.QCoh)
    (y : (objectGroupoids G).totalᵒᵖ) :
    ((pullback G.atlasToPreQuotient).obj ((fromPreQuotient G).obj A)).obj.val.obj y ≅
      ((modulePullback G.atlasToPreQuotient).obj
        ((fromPreQuotient G).obj A).obj).val.obj y :=
  { hom := (pullback_fromPreQuotient_compιIso G A).hom.val.app y
    inv := (pullback_fromPreQuotient_compιIso G A).inv.val.app y
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- `pullback_fromPreQuotient_evalIso` is evaluation of
`pullback_fromPreQuotient_compιIso`. -/
theorem pullback_fromPreQuotient_evalIso_hom (A : G.QCoh)
    (y : (objectGroupoids G).totalᵒᵖ) :
    (pullback_fromPreQuotient_evalIso G A y).hom =
      (pullback_fromPreQuotient_compιIso G A).hom.val.app y :=
  rfl

/-- Object-inclusion pullback of the Γ-sheaf, evaluated and transported to
`Γ(T, u_small^* A)` over `𝒪_{𝒮_U}`. -/
def fromPreQuotient_piStar_gammaIso (A : G.QCoh)
    (y : (objectGroupoids G).totalᵒᵖ) :
    ((pullback G.atlasToPreQuotient).obj ((fromPreQuotient G).obj A)).obj.val.obj y ≅
      (ModuleCat.restrictScalars
          ((structureSheafMap G.atlasToPreQuotient).hom.app y).hom).obj
        ((ModuleCat.restrictScalars
            ((structureSheafToPushforward G.preQuotient).hom.app
              (op (atlasToPreQuotientObj G y.unop))).hom).obj
          (gammaObj G A (atlasToPreQuotientObj G y.unop))) :=
  pullback_fromPreQuotient_evalIso G A y ≪≫
    modulePullback_evalIso G.atlasToPreQuotient
      ((fromPreQuotient G).obj A).obj y.unop ≪≫
    (ModuleCat.restrictScalars
        ((structureSheafMap G.atlasToPreQuotient).hom.app y).hom).mapIso
      (eqToIso (fromPreQuotient_obj G A (atlasToPreQuotientObj G y.unop)))

/-- `fromPreQuotient_piStar_gammaIso` is inclusion comparison, module inverse
image evaluation, and the Γ-value of `fromPreQuotient`. -/
theorem fromPreQuotient_piStar_gammaIso_eq (A : G.QCoh)
    (y : (objectGroupoids G).totalᵒᵖ) :
    fromPreQuotient_piStar_gammaIso G A y =
      pullback_fromPreQuotient_evalIso G A y ≪≫
        modulePullback_evalIso G.atlasToPreQuotient
          ((fromPreQuotient G).obj A).obj y.unop ≪≫
        (ModuleCat.restrictScalars
            ((structureSheafMap G.atlasToPreQuotient).hom.app y).hom).mapIso
          (eqToIso (fromPreQuotient_obj G A (atlasToPreQuotientObj G y.unop))) :=
  rfl

/-- After scalar transport along the object inclusion, `Γ(T, u_small^* A)` is the
value of `π_U^* A` at the corresponding object of `𝒮_U`. -/
theorem piStar_gamma_eval_eq (A : G.QCoh) (y : (objectGroupoids G).totalᵒᵖ) :
    (ModuleCat.restrictScalars
        ((structureSheafMap G.atlasToPreQuotient).hom.app y).hom).obj
      ((ModuleCat.restrictScalars
          ((structureSheafToPushforward G.preQuotient).hom.app
            (op (atlasToPreQuotientObj G y.unop))).hom).obj
        (gammaObj G A (atlasToPreQuotientObj G y.unop))) =
      ((piStar (idSpace G.U.left)).obj A.obj).obj.val.obj y :=
  sorry

/-- Evaluation of object-inclusion pullback of the Γ-sheaf identifies with
evaluation of `π_U^* A`. -/
def fromPreQuotient_piStar_evalIso (A : G.QCoh)
    (y : (objectGroupoids G).totalᵒᵖ) :
    ((pullback G.atlasToPreQuotient).obj ((fromPreQuotient G).obj A)).obj.val.obj y ≅
      ((piStar (idSpace G.U.left)).obj A.obj).obj.val.obj y :=
  fromPreQuotient_piStar_gammaIso G A y ≪≫
    eqToIso (piStar_gamma_eval_eq G A y)

/-- `fromPreQuotient_piStar_evalIso` is the Γ-transport followed by the
`π_U^*` evaluation identification. -/
theorem fromPreQuotient_piStar_evalIso_eq (A : G.QCoh)
    (y : (objectGroupoids G).totalᵒᵖ) :
    fromPreQuotient_piStar_evalIso G A y =
      fromPreQuotient_piStar_gammaIso G A y ≪≫
        eqToIso (piStar_gamma_eval_eq G A y) :=
  rfl

/-- Underlying sheaf comparison of object-inclusion pullback of the Γ-construction
with `π_U^*` of the equivariant module. -/
def fromPreQuotient_piStar_objIso (A : G.QCoh) :
    ((pullback G.atlasToPreQuotient).obj ((fromPreQuotient G).obj A)).obj ≅
      ((piStar (idSpace G.U.left)).obj A.obj).obj :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun y ↦ fromPreQuotient_piStar_evalIso G A y) sorry)

/-- Components of `fromPreQuotient_piStar_objIso` are `fromPreQuotient_piStar_evalIso`. -/
theorem fromPreQuotient_piStar_objIso_hom_app (A : G.QCoh)
    (y : (objectGroupoids G).totalᵒᵖ) :
    (fromPreQuotient_piStar_objIso G A).hom.val.app y =
      (fromPreQuotient_piStar_evalIso G A y).hom :=
  sorry

/-- Object-inclusion pullback of the Γ-sheaf identifies with `π_U^*` of the
equivariant module. -/
def fromPreQuotient_piStarIso (A : G.QCoh) :
    (pullback G.atlasToPreQuotient).obj ((fromPreQuotient G).obj A) ≅
      (piStar (idSpace G.U.left)).obj A.obj :=
  (quasiCoherentModuleProperty (objectGroupoids G)).isoMk
    (fromPreQuotient_piStar_objIso G A)

/-- `fromPreQuotient_piStarIso` is the sheaf comparison of the Γ-construction with
`π_U^*`. -/
theorem fromPreQuotient_piStarIso_eq (A : G.QCoh) :
    fromPreQuotient_piStarIso G A =
      (quasiCoherentModuleProperty (objectGroupoids G)).isoMk
        (fromPreQuotient_piStar_objIso G A) :=
  rfl

/-- Restriction of the prequotient Γ-sheaf along the object inclusion recovers the
underlying module of an equivariant object, by the `π_U^* ⊣ π_{U,*}` unit after
the Γ-to-`piStar` comparison. -/
def restrict_fromPreQuotientIso (A : G.QCoh) :
    (restrict (idSpace G.U.left)).obj
        ((pullback G.atlasToPreQuotient).obj ((fromPreQuotient G).obj A)) ≅
      A.obj :=
  (restrict (idSpace G.U.left)).mapIso (fromPreQuotient_piStarIso G A) ≪≫
    (restrict_piStarIso (idSpace G.U.left)).symm.app A.obj

/-- `restrict_fromPreQuotientIso` is restriction of the Γ-to-`piStar` comparison,
followed by the `π_U^* ⊣ π_{U,*}` unit. -/
theorem restrict_fromPreQuotientIso_eq (A : G.QCoh) :
    restrict_fromPreQuotientIso G A =
      (restrict (idSpace G.U.left)).mapIso (fromPreQuotient_piStarIso G A) ≪≫
        (restrict_piStarIso (idSpace G.U.left)).symm.app A.obj :=
  rfl

/-- `π_U^*` of the atlas restriction of `F` identifies with atlas pullback of `F`,
by the `π_U^* ⊣ π_{U,*}` counit. -/
def toGroupoid_piStar_atlasIso (F : QCoh G.quotientStack) :
    (piStar (idSpace G.U.left)).obj (atlasRestrict G F) ≅
      (pullback G.atlas).obj F :=
  (piStar_restrictIso (idSpace G.U.left)).app ((pullback G.atlas).obj F)

/-- `toGroupoid_piStar_atlasIso` is the `π_U^* ⊣ π_{U,*}` counit at atlas pullback. -/
theorem toGroupoid_piStar_atlasIso_eq (F : QCoh G.quotientStack) :
    toGroupoid_piStar_atlasIso G F =
      (piStar_restrictIso (idSpace G.U.left)).app ((pullback G.atlas).obj F) :=
  rfl

/-- Atlas pullback of `F` identifies with object-inclusion pullback of stackification
pullback, by the atlas factorization. -/
def atlas_stackificationIso (F : QCoh G.quotientStack) :
    (pullback G.atlas).obj F ≅
      (pullback G.atlasToPreQuotient).obj ((pullback G.stackificationHom).obj F) :=
  eqToIso (congrArg (fun h ↦ (pullback h).obj F) G.atlas_eq) ≪≫
    (pullback_comp G.atlasToPreQuotient G.stackificationHom).app F

/-- `atlas_stackificationIso` is `atlas_eq` then `pullback_comp`. -/
theorem atlas_stackificationIso_eq (F : QCoh G.quotientStack) :
    atlas_stackificationIso G F =
      eqToIso (congrArg (fun h ↦ (pullback h).obj F) G.atlas_eq) ≪≫
        (pullback_comp G.atlasToPreQuotient G.stackificationHom).app F :=
  rfl

/-- After object-inclusion pullback, the Γ-construction of `toGroupoid F` identifies
with stackification pullback of `F`. -/
def toGroupoid_fromPreQuotient_pullbackIso (F : QCoh G.quotientStack) :
    (pullback G.atlasToPreQuotient).obj ((fromPreQuotient G).obj ((toGroupoid G).obj F)) ≅
      (pullback G.atlasToPreQuotient).obj ((pullback G.stackificationHom).obj F) :=
  fromPreQuotient_piStarIso G ((toGroupoid G).obj F) ≪≫
    toGroupoid_piStar_atlasIso G F ≪≫ atlas_stackificationIso G F

/-- `toGroupoid_fromPreQuotient_pullbackIso` is the Γ-to-`piStar` comparison, the
`π_U^* ⊣ π_{U,*}` counit, and atlas/stackification `pullback_comp`. -/
theorem toGroupoid_fromPreQuotient_pullbackIso_eq (F : QCoh G.quotientStack) :
    toGroupoid_fromPreQuotient_pullbackIso G F =
      fromPreQuotient_piStarIso G ((toGroupoid G).obj F) ≪≫
        toGroupoid_piStar_atlasIso G F ≪≫ atlas_stackificationIso G F :=
  rfl

/-- Underlying sheaf morphism of `toGroupoid_fromPreQuotient_pullbackIso`. -/
def toGroupoid_fromPreQuotient_pullbackModulesHom (F : QCoh G.quotientStack) :
    ((pullback G.atlasToPreQuotient).obj ((fromPreQuotient G).obj ((toGroupoid G).obj F))).obj ⟶
      ((pullback G.atlasToPreQuotient).obj ((pullback G.stackificationHom).obj F)).obj :=
  (toGroupoid_fromPreQuotient_pullbackIso G F).hom.hom

/-- `toGroupoid_fromPreQuotient_pullbackModulesHom` is the underlying sheaf morphism. -/
theorem toGroupoid_fromPreQuotient_pullbackModulesHom_eq (F : QCoh G.quotientStack) :
    toGroupoid_fromPreQuotient_pullbackModulesHom G F =
      (toGroupoid_fromPreQuotient_pullbackIso G F).hom.hom :=
  rfl

/-- Underlying inverse sheaf morphism of `toGroupoid_fromPreQuotient_pullbackIso`. -/
def toGroupoid_fromPreQuotient_pullbackModulesInv (F : QCoh G.quotientStack) :
    ((pullback G.atlasToPreQuotient).obj ((pullback G.stackificationHom).obj F)).obj ⟶
      ((pullback G.atlasToPreQuotient).obj ((fromPreQuotient G).obj ((toGroupoid G).obj F))).obj :=
  (toGroupoid_fromPreQuotient_pullbackIso G F).inv.hom

/-- `toGroupoid_fromPreQuotient_pullbackModulesInv` is the underlying inverse sheaf morphism. -/
theorem toGroupoid_fromPreQuotient_pullbackModulesInv_eq (F : QCoh G.quotientStack) :
    toGroupoid_fromPreQuotient_pullbackModulesInv G F =
      (toGroupoid_fromPreQuotient_pullbackIso G F).inv.hom :=
  rfl

/-- Restriction-of-scalars comparison of the Γ-construction at the image of
`objectPoint` with object-inclusion pullback. -/
def fromPreQuotient_modulePullback_evalIso (A : G.QCoh) (x : G.preQuotient.total) :
    ((modulePullback G.atlasToPreQuotient).obj
          ((fromPreQuotient G).obj A).obj).val.obj (op (objectPoint G x)) ≅
      (ModuleCat.restrictScalars
          ((structureSheafMap G.atlasToPreQuotient).hom.app
            (op (objectPoint G x))).hom).obj
        (((fromPreQuotient G).obj A).obj.val.obj (op (atlasToPreQuotientObj G (objectPoint G x)))) :=
  modulePullback_evalIso G.atlasToPreQuotient ((fromPreQuotient G).obj A).obj
    (objectPoint G x)

/-- Restriction-of-scalars comparison of stackification pullback at the image of
`objectPoint` with evaluation at the image object. -/
def stackification_modulePullback_evalIso (F : QCoh G.quotientStack)
    (x : G.preQuotient.total) :
    ((modulePullback G.atlasToPreQuotient).obj
          ((pullback G.stackificationHom).obj F).obj).val.obj
        (op (objectPoint G x)) ≅
      (ModuleCat.restrictScalars
          ((structureSheafMap G.atlasToPreQuotient).hom.app
            (op (objectPoint G x))).hom).obj
        (((pullback G.stackificationHom).obj F).obj.val.obj (op (atlasToPreQuotientObj G (objectPoint G x)))) :=
  modulePullback_evalIso G.atlasToPreQuotient
    ((pullback G.stackificationHom).obj F).obj (objectPoint G x)

/-- The morphism of restricted-scalar modules at `objectPoint` induced by
`toGroupoid_fromPreQuotient_pullbackModulesHom`. -/
def toGroupoid_fromPreQuotient_restrictedHom (F : QCoh G.quotientStack)
    (x : G.preQuotient.total) :
    (ModuleCat.restrictScalars
        ((structureSheafMap G.atlasToPreQuotient).hom.app
          (op (objectPoint G x))).hom).obj
      (((toGroupoid G ⋙ fromPreQuotient G).obj F).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x)))) ⟶
    (ModuleCat.restrictScalars
        ((structureSheafMap G.atlasToPreQuotient).hom.app
          (op (objectPoint G x))).hom).obj
      (((pullback G.stackificationHom).obj F).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x)))) :=
  (fromPreQuotient_modulePullback_evalIso G ((toGroupoid G).obj F) x).inv ≫
    (pullback_compιIso G.atlasToPreQuotient
        ((fromPreQuotient G).obj ((toGroupoid G).obj F))).inv.val.app
      (op (objectPoint G x)) ≫
    (toGroupoid_fromPreQuotient_pullbackModulesHom G F).val.app
      (op (objectPoint G x)) ≫
    (pullback_compιIso G.atlasToPreQuotient
        ((pullback G.stackificationHom).obj F)).hom.val.app
      (op (objectPoint G x)) ≫
    (stackification_modulePullback_evalIso G F x).hom

/-- Inverse of `toGroupoid_fromPreQuotient_restrictedHom`. -/
def toGroupoid_fromPreQuotient_restrictedInv (F : QCoh G.quotientStack)
    (x : G.preQuotient.total) :
    (ModuleCat.restrictScalars
        ((structureSheafMap G.atlasToPreQuotient).hom.app
          (op (objectPoint G x))).hom).obj
      (((pullback G.stackificationHom).obj F).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x)))) ⟶
    (ModuleCat.restrictScalars
        ((structureSheafMap G.atlasToPreQuotient).hom.app
          (op (objectPoint G x))).hom).obj
      (((toGroupoid G ⋙ fromPreQuotient G).obj F).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x)))) :=
  (stackification_modulePullback_evalIso G F x).inv ≫
    (pullback_compιIso G.atlasToPreQuotient
        ((pullback G.stackificationHom).obj F)).inv.val.app
      (op (objectPoint G x)) ≫
    (toGroupoid_fromPreQuotient_pullbackModulesInv G F).val.app
      (op (objectPoint G x)) ≫
    (pullback_compιIso G.atlasToPreQuotient
        ((fromPreQuotient G).obj ((toGroupoid G).obj F))).hom.val.app
      (op (objectPoint G x)) ≫
    (fromPreQuotient_modulePullback_evalIso G ((toGroupoid G).obj F) x).hom

/-- Objectwise forward map of the Γ-construction of `toGroupoid F` toward
stackification pullback of `F`, by object transport along
`atlasToPreQuotient_objectPoint` and restriction of scalars along the
isomorphism `structureSheafMap`. -/
def toGroupoid_fromPreQuotient_app (F : QCoh G.quotientStack)
    (x : G.preQuotient.totalᵒᵖ) :
    ((toGroupoid G ⋙ fromPreQuotient G).obj F).obj.val.obj x ⟶
      ((pullback G.stackificationHom).obj F).obj.val.obj x :=
  fromPreQuotient_objectPoint_eqToHom_inv G ((toGroupoid G).obj F) x.unop ≫
    restrictScalars_reflect
      (structureSheafMap_appRingEquiv G.atlasToPreQuotient
        (op (objectPoint G x.unop)))
      (toGroupoid_fromPreQuotient_restrictedHom G F x.unop) ≫
    stackification_objectPoint_eqToHom G F x.unop

/-- Objectwise inverse map of stackification pullback of `F` toward the
Γ-construction of `toGroupoid F`. -/
def toGroupoid_fromPreQuotient_app_inv (F : QCoh G.quotientStack)
    (x : G.preQuotient.totalᵒᵖ) :
    ((pullback G.stackificationHom).obj F).obj.val.obj x ⟶
      ((toGroupoid G ⋙ fromPreQuotient G).obj F).obj.val.obj x :=
  stackification_objectPoint_eqToHom_inv G F x.unop ≫
    restrictScalars_reflect
      (structureSheafMap_appRingEquiv G.atlasToPreQuotient
        (op (objectPoint G x.unop)))
      (toGroupoid_fromPreQuotient_restrictedInv G F x.unop) ≫
    fromPreQuotient_objectPoint_eqToHom G ((toGroupoid G).obj F) x.unop

/-- Underlying sheaf comparison of `fromPreQuotient (toGroupoid F)` with
stackification pullback. -/
def toGroupoid_comp_fromPreQuotient_objIso (F : QCoh G.quotientStack) :
    ((toGroupoid G ⋙ fromPreQuotient G).obj F).obj ≅
      ((pullback G.stackificationHom).obj F).obj where
  hom :=
    { val :=
        { app := fun x ↦ toGroupoid_fromPreQuotient_app G F x
          naturality := sorry } }
  inv :=
    { val :=
        { app := fun x ↦ toGroupoid_fromPreQuotient_app_inv G F x
          naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `toGroupoid` followed by the prequotient Γ-construction is pullback along
stackification. -/
def toGroupoid_comp_fromPreQuotient :
    toGroupoid G ⋙ fromPreQuotient G ≅ pullback G.stackificationHom :=
  NatIso.ofComponents
    (fun F ↦
      (quasiCoherentModuleProperty G.preQuotient).isoMk
        (toGroupoid_comp_fromPreQuotient_objIso G F))
    sorry

/-- The unit identification of `toGroupoid` followed by `fromGroupoid`, obtained
from stackification pullback and the Γ-description of the prequotient inverse. -/
def toGroupoidEquivalence_unitIso :
    𝟭 (QCoh G.quotientStack) ≅ toGroupoid G ⋙ fromGroupoid G :=
  (pullback G.stackificationHom).asEquivalence.unitIso ≪≫
    Functor.isoWhiskerRight (toGroupoid_comp_fromPreQuotient G).symm
      (pullback G.stackificationHom).inv ≪≫
      (Functor.associator (toGroupoid G) (fromPreQuotient G)
          (pullback G.stackificationHom).inv).symm

/-- Atlas pullback of `fromGroupoid A` identifies with object-inclusion pullback of
the prequotient Γ-sheaf, via stackification. -/
def fromGroupoid_atlasPullbackIso (A : G.QCoh) :
    (pullback G.atlas).obj ((fromGroupoid G).obj A) ≅
      (pullback G.atlasToPreQuotient).obj ((fromPreQuotient G).obj A) :=
  eqToIso (congrArg (fun h ↦ (pullback h).obj ((fromGroupoid G).obj A)) G.atlas_eq) ≪≫
    (pullback_comp G.atlasToPreQuotient G.stackificationHom).app ((fromGroupoid G).obj A) ≪≫
    (pullback G.atlasToPreQuotient).mapIso ((fromGroupoid_comp_pullback G).app A)

/-- The underlying module of `toGroupoid (fromGroupoid A)` identifies with the
underlying module of `A`. -/
def fromGroupoid_toGroupoid_objIso (A : G.QCoh) :
    GroupoidAlgebraicSpace.QCoh.obj ((toGroupoid G).obj ((fromGroupoid G).obj A)) ≅
      A.obj :=
  (restrict (idSpace G.U.left)).mapIso (fromGroupoid_atlasPullbackIso G A) ≪≫
    restrict_fromPreQuotientIso G A

/-- The counit identification of `fromGroupoid` followed by `toGroupoid`. -/
def toGroupoidEquivalence_counitIso :
    fromGroupoid G ⋙ toGroupoid G ≅ 𝟭 G.QCoh :=
  NatIso.ofComponents
    (fun A ↦
      { hom :=
          System.Hom.of
            (fromGroupoid_toGroupoid_objIso G A).hom sorry
        inv :=
          System.Hom.of
            (fromGroupoid_toGroupoid_objIso G A).inv sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Proposition 96.14.3: Let `(U, R, s, t, c)` be a groupoid in algebraic spaces
over `S`. Let `𝒳 = [U / R]` be the quotient stack. The category of quasi-coherent
modules on `𝒳` is equivalent to the category of quasi-coherent modules on
`(U, R, s, t, c)`. -/
@[stacks 06WT]
def toGroupoidEquivalence : QCoh G.quotientStack ≌ G.QCoh :=
  CategoryTheory.Equivalence.mk (toGroupoid G) (fromGroupoid G)
    (toGroupoidEquivalence_unitIso G) (toGroupoidEquivalence_counitIso G)

/-- `toGroupoidEquivalence` is the functor `toGroupoid`. -/
theorem toGroupoidEquivalence_functor :
    (toGroupoidEquivalence G).functor = toGroupoid G :=
  rfl

/-- `toGroupoidEquivalence` has specified inverse `fromGroupoid`. -/
theorem toGroupoidEquivalence_inverse :
    (toGroupoidEquivalence G).inverse = fromGroupoid G :=
  rfl

/-- The functor `toGroupoid` is an equivalence of categories. -/
instance toGroupoid_isEquivalence : (toGroupoid G).IsEquivalence :=
  (toGroupoidEquivalence G).isEquivalence_functor

end AlgebraicGeometry.GroupoidsOver.QCoh
