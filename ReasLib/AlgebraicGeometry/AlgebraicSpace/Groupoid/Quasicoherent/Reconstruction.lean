/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.LocalEquivalence.Extension

/-! # Quasi-coherent reconstruction on a small quotient stack -/

@[expose] public section
set_option backward.privateInPublic true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.GroupoidsOver AlgebraicGeometry.GroupoidAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory.Functor CategoryTheory.Sheaf.InternalModule
open RingedSpace.Module.Sections.Pushforward

noncomputable section
universe u
namespace AlgebraicGeometry.GroupoidAlgebraicSpace.QuotientQCoh
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
def pointHom (x : (SmallQuotient.preQuotient G).total) : ofOver x.base ⟶ G.U.left :=
  yonedaEquiv.symm x.fiber

/-- Pullback of an equivariant module along the morphism `T ⟶ U` of an object of
`[U /ₚ R]`. -/
def pulledObj (A : G.QCoh) (x : (SmallQuotient.preQuotient G).total) :
    AlgebraicSpace.QCoh (ofOver x.base) :=
  (AlgebraicSpace.QCoh.pullback (pointHom G x)).obj A.obj

/-- Restriction of `pulledObj` to Zariski modules on the underlying scheme of
`T`. -/
def schemeObj (A : G.QCoh) (x : (SmallQuotient.preQuotient G).total) : x.base.left.Modules :=
  (AlgebraicSpace.Modules.restrictToScheme x.base).obj (pulledObj G A x).obj

/-- Global sections `Γ(T, u_small^* G)` as a module over `Γ(T, 𝒪_T)`. -/
def gammaObj (A : G.QCoh) (x : (SmallQuotient.preQuotient G).total) :
    ModuleCat.{u} (RingedSpace.globalSectionsRing x.base.left.toRingedSpace) :=
  (RingedSpace.moduleGlobalSectionsFunctor x.base.left.toRingedSpace).obj
    (schemeObj G A x)

/-- Transport of `Γ(T, u_small^* G)` to a module over `𝒪_{[U/ₚ R]}(x)`. -/
def fromPreQuotient_objModule (A : G.QCoh) (x : (SmallQuotient.preQuotient G).total) :
    ModuleCat.{u} ((structureSheaf (SmallQuotient.preQuotient G)).obj.obj (op x)) :=
  (ModuleCat.restrictScalars
      ((structureSheafToPushforward (SmallQuotient.preQuotient G)).hom.app (op x)).hom).obj
    (gammaObj G A x)

/-- The morphism `T ⟶ R` associated to the fiber of a morphism of `[U /ₚ R]`. -/
def arrowHom {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) : ofOver x.base ⟶ G.R.left :=
  yonedaEquiv.symm φ.fiber.arrow

/-- The action of `A` reindexed along the `R`-arrow of a morphism of `[U /ₚ R]`. -/
def reindexedAction (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    (AlgebraicSpace.QCoh.pullback (arrowHom G φ ≫ G.t.left)).obj A.obj ⟶
      (AlgebraicSpace.QCoh.pullback (arrowHom G φ ≫ G.s.left)).obj A.obj :=
  GroupoidAlgebraicSpace.reindexAction G.t.left G.s.left (arrowHom G φ) A.obj A.action

/-- Source of an `[U /ₚ R]`-arrow recovers the object morphism of the source. -/
private theorem arrowHom_comp_s {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    arrowHom G φ ≫ G.s.left = pointHom G x :=
  sorry

/-- Target of an `[U /ₚ R]`-arrow recovers the object morphism of the target after `φ.base`. -/
private theorem arrowHom_comp_t {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    arrowHom G φ ≫ G.t.left = ofOverMap φ.base ≫ pointHom G y :=
  sorry

/-- Identification `f_small^* (u')_small^* A ≅ (u' ∘ f)_small^* A`. -/
def pulledObj_basePullbackIso (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    (AlgebraicSpace.QCoh.pullback (ofOverMap φ.base)).obj (pulledObj G A y) ≅
      (AlgebraicSpace.QCoh.pullback (ofOverMap φ.base ≫ pointHom G y)).obj A.obj :=
  (AlgebraicSpace.QCoh.pullbackCompIso (pointHom G y) (ofOverMap φ.base)).app A.obj

/-- Reindexing `(u' ∘ f)_small^* A` along `t ∘ r = u' ∘ f`. -/
def pulledObj_targetIso (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    (AlgebraicSpace.QCoh.pullback (ofOverMap φ.base ≫ pointHom G y)).obj A.obj ≅
      (AlgebraicSpace.QCoh.pullback (arrowHom G φ ≫ G.t.left)).obj A.obj :=
  (pullbackEqIso (arrowHom_comp_t G φ).symm).app A.obj

/-- Reindexing `r_small^* s_small^* A` along `s ∘ r = u`. -/
def pulledObj_sourceIso (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    (AlgebraicSpace.QCoh.pullback (arrowHom G φ ≫ G.s.left)).obj A.obj ≅
      pulledObj G A x :=
  (pullbackEqIso (arrowHom_comp_s G φ)).app A.obj

/-- Restriction of an equivariant module along a morphism of `[U /ₚ R]`, as
pullback along `φ.base` followed by the reindexed action `α`. -/
def pulledObj_restriction (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    (AlgebraicSpace.QCoh.pullback (ofOverMap φ.base)).obj (pulledObj G A y) ⟶
      pulledObj G A x :=
  (pulledObj_basePullbackIso G A φ).hom ≫
    (pulledObj_targetIso G A φ).hom ≫
      reindexedAction G A φ ≫ (pulledObj_sourceIso G A φ).hom

/-- Global sections of `pulledObj_restriction`. -/
def gammaRestriction (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
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
def gammaObjMap {A A' : G.QCoh} (f : A ⟶ A') (x : (SmallQuotient.preQuotient G).total) :
    gammaObj G A x ⟶ gammaObj G A' x :=
  (RingedSpace.moduleGlobalSectionsFunctor x.base.left.toRingedSpace).map
    ((AlgebraicSpace.Modules.restrictToScheme x.base).map
      ((AlgebraicSpace.QCoh.inclusion (ofOver x.base)).map
        ((AlgebraicSpace.QCoh.pullback (pointHom G x)).map
          (GroupoidAlgebraicSpace.QCoh.hom f))))

/-- Global sections ring map induced by the underlying scheme morphism of `φ`. -/
def baseRingHom {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    RingedSpace.globalSectionsRing y.base.left.toRingedSpace ⟶
      RingedSpace.globalSectionsRing x.base.left.toRingedSpace :=
  φ.base.left.appTop

/-- Restriction to the source scheme of `f_small^* (u')_small^* A`. -/
def schemeObj_spacePullback (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    x.base.left.Modules :=
  (AlgebraicSpace.Modules.restrictToScheme x.base).obj
    ((AlgebraicSpace.QCoh.inclusion (ofOver x.base)).obj
      ((AlgebraicSpace.QCoh.pullback (ofOverMap φ.base)).obj (pulledObj G A y)))

/-- Direct image on `T'` of the algebraic-space pullback `f_small^* (u')_small^* A`. -/
def schemeObj_spacePushforward (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    y.base.left.Modules :=
  (AlgebraicSpace.Modules.restrictToScheme y.base).obj
    ((AlgebraicSpace.Modules.pushforward (ofOverMap φ.base)).obj
      ((AlgebraicSpace.QCoh.inclusion (ofOver x.base)).obj
        ((AlgebraicSpace.QCoh.pullback (ofOverMap φ.base)).obj (pulledObj G A y))))

/-- The pullback–pushforward unit of `ofOverMap φ.base`, restricted to the
underlying scheme of `T'`. -/
def gammaUnit (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    schemeObj G A y ⟶ schemeObj_spacePushforward G A φ :=
  (AlgebraicSpace.Modules.restrictToScheme y.base).map
    ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction
        (ofOverMap φ.base)).unit.app (pulledObj G A y).obj)

/-- Global sections of the algebraic-space adjunction unit. -/
def gammaSpacePullback (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    gammaObj G A y ⟶
      (RingedSpace.moduleGlobalSectionsFunctor y.base.left.toRingedSpace).obj
        (schemeObj_spacePushforward G A φ) :=
  (RingedSpace.moduleGlobalSectionsFunctor y.base.left.toRingedSpace).map
    (gammaUnit G A φ)

/-- The morphism of ringed spaces underlying `φ.base`. -/
def baseShHom {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    x.base.left.toRingedSpace ⟶ y.base.left.toRingedSpace :=
  φ.base.left.toLRSHom.toShHom

/-- Ringed-space direct image of `schemeObj_spacePullback` along `φ.base`. -/
def schemeObj_ringedPushforward (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    y.base.left.toRingedSpace.Modules :=
  (RingedSpace.Hom.pushforward (baseShHom G φ)).obj
    ((Scheme.Modules.toRingedSpace x.base.left).obj (schemeObj_spacePullback G A φ))

/-- First leg of restriction: global sections of the algebraic-space
adjunction unit, then the ringed-space identification of direct-image
sections with scalar-restricted sections of `schemeObj_spacePullback`. -/
def gammaFirstLeg (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    gammaObj G A y ⟶
      (ModuleCat.restrictScalars (baseRingHom G φ).hom).obj
        ((RingedSpace.moduleGlobalSectionsFunctor x.base.left.toRingedSpace).obj
          (schemeObj_spacePullback G A φ)) :=
  gammaSpacePullback G A φ ≫
    (RingedSpace.moduleGlobalSectionsFunctor y.base.left.toRingedSpace).map
      ((AlgebraicSpace.DerivedQCoh.SchemeRestriction.pushforwardSquareIso φ.base).hom.app
      ((AlgebraicSpace.QCoh.inclusion (ofOver x.base)).obj
        ((AlgebraicSpace.QCoh.pullback (ofOverMap φ.base)).obj (pulledObj G A y)))) ≫
    (globalSectionIso (baseShHom G φ)
        ((Scheme.Modules.toRingedSpace x.base.left).obj
          (schemeObj_spacePullback G A φ))).inv

/-- The Γ-level restriction map: pullback along `φ.base`, then the reindexed action. -/
def gammaObj_restriction (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    gammaObj G A y ⟶
      (ModuleCat.restrictScalars (baseRingHom G φ).hom).obj (gammaObj G A x) :=
  gammaFirstLeg G A φ ≫
    (ModuleCat.restrictScalars (baseRingHom G φ).hom).map (gammaRestriction G A φ)

/-- The ring-hom equality underlying scalar transport along `φ` and the
structure-sheaf comparison. -/
private theorem structureSheaf_baseRing_comp {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    (baseRingHom G φ).hom.comp
        ((structureSheafToPushforward (SmallQuotient.preQuotient G)).hom.app (op y)).hom =
      ((structureSheafToPushforward (SmallQuotient.preQuotient G)).hom.app (op x)).hom.comp
        ((structureSheaf (SmallQuotient.preQuotient G)).obj.map φ.op).hom :=
  sorry

/-- Restriction map of the prequotient module presheaf along a morphism of
`[U /ₚ R]`, given by pullback of sections along the underlying scheme map
followed by the reindexed action, then scalar transport to `𝒪_{[U/ₚ R]}(x)`. -/
def fromPreQuotient_mapModule (A : G.QCoh) {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    fromPreQuotient_objModule G A y ⟶
      (ModuleCat.restrictScalars
          ((structureSheaf (SmallQuotient.preQuotient G)).obj.map φ.op).hom).obj
        (fromPreQuotient_objModule G A x) :=
  (ModuleCat.restrictScalars
      ((structureSheafToPushforward (SmallQuotient.preQuotient G)).hom.app (op y)).hom).map
      (gammaObj_restriction G A φ) ≫
    (ModuleCat.restrictScalarsComp'
        ((structureSheafToPushforward (SmallQuotient.preQuotient G)).hom.app (op y)).hom
        (baseRingHom G φ).hom
        ((baseRingHom G φ).hom.comp
          ((structureSheafToPushforward (SmallQuotient.preQuotient G)).hom.app (op y)).hom)
        rfl).inv.app (gammaObj G A x) ≫
    (ModuleCat.restrictScalarsComp'
        ((structureSheaf (SmallQuotient.preQuotient G)).obj.map φ.op).hom
        ((structureSheafToPushforward (SmallQuotient.preQuotient G)).hom.app (op x)).hom
        ((baseRingHom G φ).hom.comp
          ((structureSheafToPushforward (SmallQuotient.preQuotient G)).hom.app (op y)).hom)
        (structureSheaf_baseRing_comp G φ)).hom.app (gammaObj G A x)

/-- Global-section restriction respects identity and composition with the
specified scalar-change isomorphisms. -/
private theorem fromPreQuotientPresheaf_laws (A : G.QCoh) :
    let R := (structureSheaf (SmallQuotient.preQuotient G)).obj
    (∀ x : (SmallQuotient.preQuotient G).totalᵒᵖ,
      fromPreQuotient_mapModule G A (𝟙 x).unop =
        (ModuleCat.restrictScalarsId' (R.map (𝟙 x)).hom
          (congrArg RingCat.Hom.hom (R.map_id x))).inv.app _) ∧
    (∀ {x y z : (SmallQuotient.preQuotient G).totalᵒᵖ} (a : x ⟶ y) (b : y ⟶ z),
      fromPreQuotient_mapModule G A (a ≫ b).unop =
        fromPreQuotient_mapModule G A a.unop ≫
          (ModuleCat.restrictScalars (R.map a).hom).map
            (fromPreQuotient_mapModule G A b.unop) ≫
          (ModuleCat.restrictScalarsComp' (R.map a).hom (R.map b).hom
            (R.map (a ≫ b)).hom (congrArg RingCat.Hom.hom (R.map_comp a b))).inv.app _) := sorry

/-- The module presheaf on the groupoid prestack has the global sections of
its reindexed equivariant module as its values. -/
def fromPreQuotientPresheaf (A : G.QCoh) :
    PresheafOfModules.{u} (structureSheaf (SmallQuotient.preQuotient G)).obj where
  obj x := fromPreQuotient_objModule G A x.unop
  map φ := fromPreQuotient_mapModule G A φ.unop
  map_id := (fromPreQuotientPresheaf_laws G A).1
  map_comp := (fromPreQuotientPresheaf_laws G A).2

/-- Reindexed equivariant global sections satisfy fppf descent. -/
private theorem fromPreQuotientSheaf_isSheaf (A : G.QCoh) :
    Presheaf.IsSheaf (SmallQuotient.preQuotient G).fppfTopology
      (fromPreQuotientPresheaf G A).presheaf := sorry

/-- The module sheaf of reindexed equivariant global sections on the groupoid prestack. -/
def fromPreQuotientSheaf (A : G.QCoh) :
    SheafOfModules.{u} (structureSheaf (SmallQuotient.preQuotient G)) where
  val := fromPreQuotientPresheaf G A
  isSheaf := fromPreQuotientSheaf_isSheaf G A

/-- Scalar-restricted global sections of an equivariant morphism. -/
private def sectionMap {A A' : G.QCoh} (f : A ⟶ A')
    (x : (SmallQuotient.preQuotient G).totalᵒᵖ) :
    (fromPreQuotientPresheaf G A).obj x ⟶ (fromPreQuotientPresheaf G A').obj x :=
  (ModuleCat.restrictScalars
    ((structureSheafToPushforward (SmallQuotient.preQuotient G)).hom.app x).hom).map
      (gammaObjMap G f x.unop)

/-- Equivariant morphisms commute with reindexed restriction of global sections. -/
private theorem fromPreQuotientSheafMap_laws {A A' : G.QCoh} (f : A ⟶ A') :
    ∀ {x y : (SmallQuotient.preQuotient G).totalᵒᵖ} (a : x ⟶ y),
      (fromPreQuotientPresheaf G A).map a ≫
        (ModuleCat.restrictScalars
          ((structureSheaf (SmallQuotient.preQuotient G)).obj.map a).hom).map
            (sectionMap G f y) =
        sectionMap G f x ≫ (fromPreQuotientPresheaf G A').map a := sorry

/-- An equivariant morphism acts on the module sheaves by its actual reindexed
maps of global sections. -/
def fromPreQuotientSheafMap {A A' : G.QCoh} (f : A ⟶ A') :
    fromPreQuotientSheaf G A ⟶ fromPreQuotientSheaf G A' where
  val := { app := sectionMap G f, naturality := fromPreQuotientSheafMap_laws G f }

/-- Reconstruction of equivariant morphisms preserves identities and composition. -/
private theorem fromPreQuotientModules_laws :
    (∀ A : G.QCoh, fromPreQuotientSheafMap G (𝟙 A) = 𝟙 _) ∧
    (∀ {A A' A'' : G.QCoh} (a : A ⟶ A') (b : A' ⟶ A''),
      fromPreQuotientSheafMap G (a ≫ b) =
        fromPreQuotientSheafMap G a ≫ fromPreQuotientSheafMap G b) := sorry

/-- Equivariant modules determine module sheaves on the groupoid prestack by
reindexed global sections. -/
def fromPreQuotientModules :
    G.QCoh ⥤ SheafOfModules.{u} (structureSheaf (SmallQuotient.preQuotient G)) where
  obj A := fromPreQuotientSheaf G A
  map f := fromPreQuotientSheafMap G f
  map_id := (fromPreQuotientModules_laws G).1
  map_comp := (fromPreQuotientModules_laws G).2

/-- Reconstruction of an equivariant quasi-coherent module is quasi-coherent. -/
private theorem fromPreQuotient_isQuasicoherent (A : G.QCoh) :
    (fromPreQuotientSheaf G A).IsQuasicoherent := sorry

/-- Reindexed equivariant global sections give a quasi-coherent module on
the groupoid prestack. -/
def fromPreQuotient : G.QCoh ⥤ GroupoidsOver.QCoh (SmallQuotient.preQuotient G) :=
  (quasiCoherentModuleProperty (SmallQuotient.preQuotient G)).lift (fromPreQuotientModules G)
    (fromPreQuotient_isQuasicoherent G)

/-- Evaluation of reconstructed prestack modules is the scalar-restricted
module of global sections of the reindexed equivariant module. -/
theorem fromPreQuotient_obj (A : G.QCoh) (x : (SmallQuotient.preQuotient G).total) :
    ((fromPreQuotient G).obj A).obj.val.obj (op x) =
      fromPreQuotient_objModule G A x := rfl

/-- Restriction in the reconstructed prestack module is pullback of global
sections followed by the reindexed action and its coefficient transport. -/
theorem fromPreQuotient_map (A : G.QCoh)
    {x y : (SmallQuotient.preQuotient G).total} (φ : x ⟶ y) :
    ((fromPreQuotient G).obj A).obj.val.map φ.op =
      fromPreQuotient_mapModule G A φ := rfl

/-- Compatible-section extension transfers the reconstructed prequotient module
sheaf to the quotient stack. -/
def fromGroupoidStack : G.QCoh ⥤ GroupoidsOver.QCoh (SmallQuotient.quotientStack G) :=
  fromPreQuotient G ⋙
    (LocalEquivalenceModules.qcohEquivalence (SmallQuotient.stackificationHom G)
      (FiberedCategoryOver.Groupoids.Hom.IsStackification.isLocalEquivalence
        (SmallQuotient.stackificationHom_isStackification G))).inverse

/-- Pullback of reconstructed quotient modules recovers the prequotient
module sheaf with its original section maps. -/
def fromGroupoidStack_comp_pullback :
    fromGroupoidStack G ⋙ GroupoidsOver.QCoh.pullback (SmallQuotient.stackificationHom G) ≅
      fromPreQuotient G :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (fromPreQuotient G)
    (LocalEquivalenceModules.qcohEquivalence (SmallQuotient.stackificationHom G)
      (FiberedCategoryOver.Groupoids.Hom.IsStackification.isLocalEquivalence
        (SmallQuotient.stackificationHom_isStackification G))).counitIso

end AlgebraicGeometry.GroupoidAlgebraicSpace.QuotientQCoh
