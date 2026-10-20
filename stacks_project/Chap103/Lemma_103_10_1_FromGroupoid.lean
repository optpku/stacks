/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap75.Lemma_75_21_1_Pullback
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import stacks_project.Chap78.Lemma_78_12_3_QCoh
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf
public import stacks_project.Chap96.Lemma_96_13_2

/-!
# Inverse functor from groupoid QCoh to quotient-stack QCoh

This reconstruction of Sheaves on Stacks, Proposition 96.14.3 avoids the
`etaleRingedSite` diamond with `LQCoh^{fbc}` by inlining the fppf
structure-sheaf comparison instead of importing Lemma 96.11.3.

An equivariant quasi-coherent module `(G, α)` on `(U, R, s, t, c)` determines a
quasi-coherent module on `[U /ₚ R]` with value `Γ(T, u_small^* G)` at an object
`(T, u)`, and restriction along `(f, r)` given by pullback along `f` followed by
`α` along `r`. Stackification then transfers this to `[U / R]`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalModule
open RingedSpace.Module.Sections.Pushforward

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- Unfolding of fppf `𝒪_X` as `p.op ⋙ Γ`, then `forget₂`. -/
def structureSheafToPushforward (X : GroupoidsOver S) :
    (structureSheaf X).obj ≅
      (X.p.op ⋙ ((Over.forget S).op ⋙ Scheme.Γ)) ⋙
        forget₂ CommRingCat.{u} RingCat.{u} :=
  (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
      (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).app
    (StandardTopology.Big.structureSheaf .fppf S) ≪≫
  (Functor.associator X.p.op ((Over.forget S).op ⋙ Scheme.Γ)
      (forget₂ CommRingCat.{u} RingCat.{u})).symm

/-- The morphism `T ⟶ U` of algebraic spaces associated to a `T`-valued point of
`U` in `[U /ₚ R]`. -/
def pointHom (x : G.preQuotient.total) : ofOver x.base ⟶ G.U.left :=
  yonedaEquiv.symm x.fiber

/-- `pointHom x` is the Yoneda equivalent of the fiber of `x`. -/
theorem pointHom_eq (x : G.preQuotient.total) :
    pointHom G x = yonedaEquiv.symm x.fiber :=
  rfl

/-- Pullback of an equivariant module along the morphism `T ⟶ U` of an object of
`[U /ₚ R]`. -/
def pulledObj (A : G.QCoh) (x : G.preQuotient.total) :
    AlgebraicSpace.QCoh (ofOver x.base) :=
  (AlgebraicSpace.QCoh.pullback (pointHom G x)).obj A.obj

/-- Restriction of `pulledObj` to Zariski modules on the underlying scheme of
`T`. -/
def schemeObj (A : G.QCoh) (x : G.preQuotient.total) : x.base.left.Modules :=
  (AlgebraicSpace.Modules.restrictToScheme x.base).obj (pulledObj G A x).obj

/-- Global sections `Γ(T, u_small^* G)` as a module over `Γ(T, 𝒪_T)`. -/
def gammaObj (A : G.QCoh) (x : G.preQuotient.total) :
    ModuleCat.{u} (RingedSpace.globalSectionsRing x.base.left.toRingedSpace) :=
  (RingedSpace.moduleGlobalSectionsFunctor x.base.left.toRingedSpace).obj
    (schemeObj G A x)

/-- Transport of `Γ(T, u_small^* G)` to a module over `𝒪_{[U/ₚ R]}(x)`. -/
def fromPreQuotient_objModule (A : G.QCoh) (x : G.preQuotient.total) :
    ModuleCat.{u} ((structureSheaf G.preQuotient).obj.obj (op x)) :=
  (ModuleCat.restrictScalars
      ((structureSheafToPushforward G.preQuotient).hom.app (op x)).hom).obj
    (gammaObj G A x)

/-- The morphism `T ⟶ R` associated to the fiber of a morphism of `[U /ₚ R]`. -/
def arrowHom {x y : G.preQuotient.total} (φ : x ⟶ y) : ofOver x.base ⟶ G.R.left :=
  yonedaEquiv.symm φ.fiber.arrow

/-- The action of `A` reindexed along the `R`-arrow of a morphism of `[U /ₚ R]`. -/
def reindexedAction (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    (AlgebraicSpace.QCoh.pullback (arrowHom G φ ≫ G.t.left)).obj A.obj ⟶
      (AlgebraicSpace.QCoh.pullback (arrowHom G φ ≫ G.s.left)).obj A.obj :=
  GroupoidAlgebraicSpace.reindexAction G.t.left G.s.left (arrowHom G φ) A.obj A.action

/-- Source of an `[U /ₚ R]`-arrow recovers the object morphism of the source. -/
theorem arrowHom_comp_s {x y : G.preQuotient.total} (φ : x ⟶ y) :
    arrowHom G φ ≫ G.s.left = pointHom G x :=
  sorry

/-- Target of an `[U /ₚ R]`-arrow recovers the object morphism of the target after `φ.base`. -/
theorem arrowHom_comp_t {x y : G.preQuotient.total} (φ : x ⟶ y) :
    arrowHom G φ ≫ G.t.left = ofOverMap φ.base ≫ pointHom G y :=
  sorry

/-- Identification `f_small^* (u')_small^* A ≅ (u' ∘ f)_small^* A`. -/
def pulledObj_basePullbackIso (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    (AlgebraicSpace.QCoh.pullback (ofOverMap φ.base)).obj (pulledObj G A y) ≅
      (AlgebraicSpace.QCoh.pullback (ofOverMap φ.base ≫ pointHom G y)).obj A.obj :=
  (pullbackCompIso (ofOverMap φ.base) (pointHom G y)).symm.app A.obj

/-- Reindexing `(u' ∘ f)_small^* A` along `t ∘ r = u' ∘ f`. -/
def pulledObj_targetIso (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    (AlgebraicSpace.QCoh.pullback (ofOverMap φ.base ≫ pointHom G y)).obj A.obj ≅
      (AlgebraicSpace.QCoh.pullback (arrowHom G φ ≫ G.t.left)).obj A.obj :=
  (pullbackEqIso (arrowHom_comp_t G φ).symm).app A.obj

/-- Reindexing `r_small^* s_small^* A` along `s ∘ r = u`. -/
def pulledObj_sourceIso (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    (AlgebraicSpace.QCoh.pullback (arrowHom G φ ≫ G.s.left)).obj A.obj ≅
      pulledObj G A x :=
  (pullbackEqIso (arrowHom_comp_s G φ)).app A.obj

/-- Restriction of an equivariant module along a morphism of `[U /ₚ R]`, as
pullback along `φ.base` followed by the reindexed action `α`. -/
def pulledObj_restriction (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    (AlgebraicSpace.QCoh.pullback (ofOverMap φ.base)).obj (pulledObj G A y) ⟶
      pulledObj G A x :=
  (pulledObj_basePullbackIso G A φ).hom ≫
    (pulledObj_targetIso G A φ).hom ≫
      reindexedAction G A φ ≫ (pulledObj_sourceIso G A φ).hom

/-- Global sections of `pulledObj_restriction`. -/
def gammaRestriction (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    (RingedSpace.moduleGlobalSectionsFunctor x.base.left.toRingedSpace).obj
      ((AlgebraicSpace.Modules.restrictToScheme x.base).obj
        ((AlgebraicSpace.QCoh.inclusion (ofOver x.base)).obj
          ((AlgebraicSpace.QCoh.pullback (ofOverMap φ.base)).obj (pulledObj G A y)))) ⟶
      gammaObj G A x :=
  (RingedSpace.moduleGlobalSectionsFunctor x.base.left.toRingedSpace).map
    ((AlgebraicSpace.Modules.restrictToScheme x.base).map
      ((AlgebraicSpace.QCoh.inclusion (ofOver x.base)).map
        (pulledObj_restriction G A φ)))

/-- A morphism of equivariant modules induces a map of global sections at an
object of `[U /ₚ R]`. -/
def gammaObjMap {A A' : G.QCoh} (f : A ⟶ A') (x : G.preQuotient.total) :
    gammaObj G A x ⟶ gammaObj G A' x :=
  (RingedSpace.moduleGlobalSectionsFunctor x.base.left.toRingedSpace).map
    ((AlgebraicSpace.Modules.restrictToScheme x.base).map
      ((AlgebraicSpace.QCoh.inclusion (ofOver x.base)).map
        ((AlgebraicSpace.QCoh.pullback (pointHom G x)).map
          (GroupoidAlgebraicSpace.QCoh.hom f))))

/-- Global sections ring map induced by the underlying scheme morphism of `φ`. -/
def baseRingHom {x y : G.preQuotient.total} (φ : x ⟶ y) :
    RingedSpace.globalSectionsRing y.base.left.toRingedSpace ⟶
      RingedSpace.globalSectionsRing x.base.left.toRingedSpace :=
  φ.base.left.appTop

/-- Restriction to the source scheme of `f_small^* (u')_small^* A`. -/
def schemeObj_spacePullback (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    x.base.left.Modules :=
  (AlgebraicSpace.Modules.restrictToScheme x.base).obj
    ((AlgebraicSpace.QCoh.inclusion (ofOver x.base)).obj
      ((AlgebraicSpace.QCoh.pullback (ofOverMap φ.base)).obj (pulledObj G A y)))

/-- Direct image on `T'` of the algebraic-space pullback `f_small^* (u')_small^* A`. -/
def schemeObj_spacePushforward (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    y.base.left.Modules :=
  (AlgebraicSpace.Modules.restrictToScheme y.base).obj
    ((AlgebraicSpace.Modules.pushforward (ofOverMap φ.base)).obj
      ((AlgebraicSpace.QCoh.inclusion (ofOver x.base)).obj
        ((AlgebraicSpace.QCoh.pullback (ofOverMap φ.base)).obj (pulledObj G A y))))

/-- The pullback–pushforward unit of `ofOverMap φ.base`, restricted to the
underlying scheme of `T'`. -/
def gammaUnit (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    schemeObj G A y ⟶ schemeObj_spacePushforward G A φ :=
  (AlgebraicSpace.Modules.restrictToScheme y.base).map
    ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (ofOverMap φ.base)).unit.app (pulledObj G A y).obj)

/-- `gammaUnit` is restriction of the algebraic-space adjunction unit. -/
theorem gammaUnit_eq (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    gammaUnit G A φ =
      (AlgebraicSpace.Modules.restrictToScheme y.base).map
        ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction
            (ofOverMap φ.base)).unit.app (pulledObj G A y).obj) :=
  rfl

/-- Global sections of the algebraic-space adjunction unit. -/
def gammaSpacePullback (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    gammaObj G A y ⟶
      (RingedSpace.moduleGlobalSectionsFunctor y.base.left.toRingedSpace).obj
        (schemeObj_spacePushforward G A φ) :=
  (RingedSpace.moduleGlobalSectionsFunctor y.base.left.toRingedSpace).map
    (gammaUnit G A φ)

/-- `gammaSpacePullback` is global sections of `gammaUnit`. -/
theorem gammaSpacePullback_eq (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    gammaSpacePullback G A φ =
      (RingedSpace.moduleGlobalSectionsFunctor y.base.left.toRingedSpace).map
        (gammaUnit G A φ) :=
  rfl

/-- The morphism of ringed spaces underlying `φ.base`. -/
def baseShHom {x y : G.preQuotient.total} (φ : x ⟶ y) :
    x.base.left.toRingedSpace ⟶ y.base.left.toRingedSpace :=
  φ.base.left.toLRSHom.toShHom

/-- Ringed-space direct image of `schemeObj_spacePullback` along `φ.base`. -/
def schemeObj_ringedPushforward (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    y.base.left.toRingedSpace.Modules :=
  (RingedSpace.Hom.pushforward (baseShHom G φ)).obj
    ((Scheme.Modules.toRingedSpace x.base.left).obj (schemeObj_spacePullback G A φ))

/-- `schemeObj_ringedPushforward` is ringed-space pushforward of
`schemeObj_spacePullback`. -/
theorem schemeObj_ringedPushforward_eq (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    schemeObj_ringedPushforward G A φ =
      (RingedSpace.Hom.pushforward (baseShHom G φ)).obj
        ((Scheme.Modules.toRingedSpace x.base.left).obj (schemeObj_spacePullback G A φ)) :=
  rfl

/-- The underived algebraic-space/ringed-space pushforward comparison at the
pullback of `pulledObj y` along `φ.base`. -/
def spacePushforward_ringedPushforwardHom (A : G.QCoh)
    {x y : G.preQuotient.total} (φ : x ⟶ y) :
    (Scheme.Modules.toRingedSpace y.base.left).obj (schemeObj_spacePushforward G A φ) ⟶
      schemeObj_ringedPushforward G A φ :=
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SchemeRestriction.pushforwardSquareHom φ.base).app
    ((AlgebraicSpace.QCoh.inclusion (ofOver x.base)).obj
      ((AlgebraicSpace.QCoh.pullback (ofOverMap φ.base)).obj (pulledObj G A y)))

/-- `spacePushforward_ringedPushforwardHom` is the underived comparison of
`AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SchemeRestriction.pushforwardSquareHom`. -/
theorem spacePushforward_ringedPushforwardHom_eq (A : G.QCoh)
    {x y : G.preQuotient.total} (φ : x ⟶ y) :
    spacePushforward_ringedPushforwardHom G A φ =
      (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SchemeRestriction.pushforwardSquareHom φ.base).app
        ((AlgebraicSpace.QCoh.inclusion (ofOver x.base)).obj
          ((AlgebraicSpace.QCoh.pullback (ofOverMap φ.base)).obj (pulledObj G A y))) :=
  rfl

/-- The underived algebraic-space/ringed-space pushforward comparison is an
isomorphism. -/
instance spacePushforward_ringedPushforwardHom_isIso (A : G.QCoh)
    {x y : G.preQuotient.total} (φ : x ⟶ y) :
    IsIso (spacePushforward_ringedPushforwardHom G A φ) := by
  change IsIso ((AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SchemeRestriction.pushforwardSquareIso φ.base).hom.app
    ((AlgebraicSpace.QCoh.inclusion (ofOver x.base)).obj
      ((AlgebraicSpace.QCoh.pullback (ofOverMap φ.base)).obj (pulledObj G A y))))
  infer_instance

/-- Comparison of algebraic-space pushforward, restricted to the scheme of `T'`,
with ringed-space pushforward of `schemeObj_spacePullback`. -/
def spacePushforward_ringedPushforwardIso (A : G.QCoh)
    {x y : G.preQuotient.total} (φ : x ⟶ y) :
    (Scheme.Modules.toRingedSpace y.base.left).obj (schemeObj_spacePushforward G A φ) ≅
      schemeObj_ringedPushforward G A φ :=
  asIso (spacePushforward_ringedPushforwardHom G A φ)

/-- `spacePushforward_ringedPushforwardIso` is `asIso` of the underived
pushforward comparison. -/
theorem spacePushforward_ringedPushforwardIso_eq (A : G.QCoh)
    {x y : G.preQuotient.total} (φ : x ⟶ y) :
    spacePushforward_ringedPushforwardIso G A φ =
      asIso (spacePushforward_ringedPushforwardHom G A φ) :=
  rfl

/-- First leg of restriction: global sections of the algebraic-space
adjunction unit, then the ringed-space identification of direct-image
sections with scalar-restricted sections of `schemeObj_spacePullback`. -/
def gammaFirstLeg (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    gammaObj G A y ⟶
      (ModuleCat.restrictScalars (baseRingHom G φ).hom).obj
        ((RingedSpace.moduleGlobalSectionsFunctor x.base.left.toRingedSpace).obj
          (schemeObj_spacePullback G A φ)) :=
  gammaSpacePullback G A φ ≫
    (RingedSpace.moduleGlobalSectionsFunctor y.base.left.toRingedSpace).map
      (spacePushforward_ringedPushforwardIso G A φ).hom ≫
    (globalSectionIso (baseShHom G φ)
        ((Scheme.Modules.toRingedSpace x.base.left).obj
          (schemeObj_spacePullback G A φ))).inv

/-- `gammaFirstLeg` is the adjunction unit, the pushforward comparison, and
`globalSectionIso`. -/
theorem gammaFirstLeg_eq (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    gammaFirstLeg G A φ =
      gammaSpacePullback G A φ ≫
        (RingedSpace.moduleGlobalSectionsFunctor y.base.left.toRingedSpace).map
          (spacePushforward_ringedPushforwardIso G A φ).hom ≫
        (globalSectionIso (baseShHom G φ)
            ((Scheme.Modules.toRingedSpace x.base.left).obj
              (schemeObj_spacePullback G A φ))).inv :=
  rfl

/-- The Γ-level restriction map: pullback along `φ.base`, then the reindexed action. -/
def gammaObj_restriction (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    gammaObj G A y ⟶
      (ModuleCat.restrictScalars (baseRingHom G φ).hom).obj (gammaObj G A x) :=
  gammaFirstLeg G A φ ≫
    (ModuleCat.restrictScalars (baseRingHom G φ).hom).map (gammaRestriction G A φ)

/-- The ring-hom equality underlying scalar transport along `φ` and the
structure-sheaf comparison. -/
theorem structureSheaf_baseRing_comp {x y : G.preQuotient.total} (φ : x ⟶ y) :
    (baseRingHom G φ).hom.comp
        ((structureSheafToPushforward G.preQuotient).hom.app (op y)).hom =
      ((structureSheafToPushforward G.preQuotient).hom.app (op x)).hom.comp
        ((structureSheaf G.preQuotient).obj.map φ.op).hom :=
  sorry

/-- Restriction map of the prequotient module presheaf along a morphism of
`[U /ₚ R]`, given by pullback of sections along the underlying scheme map
followed by the reindexed action, then scalar transport to `𝒪_{[U/ₚ R]}(x)`. -/
def fromPreQuotient_mapModule (A : G.QCoh) {x y : G.preQuotient.total} (φ : x ⟶ y) :
    fromPreQuotient_objModule G A y ⟶
      (ModuleCat.restrictScalars
          ((structureSheaf G.preQuotient).obj.map φ.op).hom).obj
        (fromPreQuotient_objModule G A x) :=
  (ModuleCat.restrictScalars
      ((structureSheafToPushforward G.preQuotient).hom.app (op y)).hom).map
      (gammaObj_restriction G A φ) ≫
    (ModuleCat.restrictScalarsComp'
        ((structureSheafToPushforward G.preQuotient).hom.app (op y)).hom
        (baseRingHom G φ).hom
        ((baseRingHom G φ).hom.comp
          ((structureSheafToPushforward G.preQuotient).hom.app (op y)).hom)
        rfl).inv.app (gammaObj G A x) ≫
    (ModuleCat.restrictScalarsComp'
        ((structureSheaf G.preQuotient).obj.map φ.op).hom
        ((structureSheafToPushforward G.preQuotient).hom.app (op x)).hom
        ((baseRingHom G φ).hom.comp
          ((structureSheafToPushforward G.preQuotient).hom.app (op y)).hom)
        (structureSheaf_baseRing_comp G φ)).hom.app (gammaObj G A x)

/-- The module presheaf on `[U /ₚ R]` with value `Γ(T, u_small^* G)`. -/
def fromPreQuotientPresheaf (A : G.QCoh) :
    PresheafOfModules.{u} (structureSheaf G.preQuotient).obj where
  obj x := fromPreQuotient_objModule G A x.unop
  map φ := fromPreQuotient_mapModule G A φ.unop
  map_id := sorry
  map_comp := sorry

/-- The sheaf of modules on `[U /ₚ R]` with value `Γ(T, u_small^* G)`. -/
def fromPreQuotientSheaf (A : G.QCoh) :
    SheafOfModules.{u} (structureSheaf G.preQuotient) where
  val := fromPreQuotientPresheaf G A
  isSheaf := sorry

/-- A morphism of equivariant modules induces a morphism of prequotient module
sheaves, by applying pullback, restriction to schemes, and global sections. -/
def fromPreQuotientSheafMap {A A' : G.QCoh} (f : A ⟶ A') :
    fromPreQuotientSheaf G A ⟶ fromPreQuotientSheaf G A' where
  val :=
    PresheafOfModules.homMk
      { app := fun x =>
          (forget₂
              (ModuleCat.{u}
                (RingedSpace.globalSectionsRing x.unop.base.left.toRingedSpace))
              AddCommGrpCat.{u}).map
            (gammaObjMap G f x.unop)
        naturality := sorry }
      sorry

/-- The functor sending an equivariant module on `(U, R, s, t, c)` to the
quasi-coherent module on `[U /ₚ R]` with values `Γ(T, u_small^* G)`. -/
def fromPreQuotientModules : G.QCoh ⥤ SheafOfModules.{u} (structureSheaf G.preQuotient) where
  obj A := fromPreQuotientSheaf G A
  map f := fromPreQuotientSheafMap G f
  map_id := sorry
  map_comp := sorry

/-- The functor sending an equivariant module on `(U, R, s, t, c)` to the
quasi-coherent module on `[U /ₚ R]` with values `Γ(T, u_small^* G)`. -/
def fromPreQuotient : G.QCoh ⥤ QCoh G.preQuotient :=
  (quasiCoherentModuleProperty G.preQuotient).lift (fromPreQuotientModules G)
    fun _ => sorry

/-- The value of `fromPreQuotient A` at an object `x = (T, u)` is `Γ(T, u_small^* G)`,
transported to a module over `𝒪_{[U/ₚ R]}(x)`. -/
theorem fromPreQuotient_obj (A : G.QCoh) (x : G.preQuotient.total) :
    ((fromPreQuotient G).obj A).obj.val.obj (op x) =
      fromPreQuotient_objModule G A x :=
  rfl

/-- Pullback of quasi-coherent modules along stackification of `[U /ₚ R]` is an
equivalence. -/
instance pullback_stackificationHom_isEquivalence :
    (pullback G.stackificationHom).IsEquivalence :=
  pullback_isEquivalence_of_isStackification G.stackificationHom
    G.stackificationHom_isStackification

/-- The functor sending an equivariant module on `(U, R, s, t, c)` to a
quasi-coherent module on `[U / R]`, by constructing the prequotient sheaf and
transporting along stackification. This is `q₁` in the source of Stacks Tag 0778. -/
def fromGroupoidStack : G.QCoh ⥤ QCoh G.quotientStack :=
  fromPreQuotient G ⋙ (pullback G.stackificationHom).inv

/-- After pullback along stackification, `fromGroupoid` recovers the prequotient
sheaf of values `Γ(T, u_small^* G)`. -/
def fromGroupoidStack_comp_pullback :
    fromGroupoidStack G ⋙ pullback G.stackificationHom ≅ fromPreQuotient G :=
  Functor.associator (fromPreQuotient G) (pullback G.stackificationHom).inv
      (pullback G.stackificationHom) ≪≫
    Functor.isoWhiskerLeft (fromPreQuotient G)
      (pullback G.stackificationHom).asEquivalence.counitIso

/-- `fromGroupoid_comp_pullback` is the counit of stackification pullback after
the associator. -/
theorem fromGroupoidStack_comp_pullback_eq :
    fromGroupoidStack_comp_pullback G =
      Functor.associator (fromPreQuotient G) (pullback G.stackificationHom).inv
          (pullback G.stackificationHom) ≪≫
        Functor.isoWhiskerLeft (fromPreQuotient G)
          (pullback G.stackificationHom).asEquivalence.counitIso :=
  rfl

end AlgebraicGeometry.GroupoidsOver.QCoh
