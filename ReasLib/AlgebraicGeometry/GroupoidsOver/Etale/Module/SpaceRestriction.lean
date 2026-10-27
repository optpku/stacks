/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison.Etale
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.TwoCell
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SmallEtaleComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange

/-! # Restriction of flat-base-change modules to algebraic spaces -/

@[expose] public section
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry Opposite
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section
universe u
namespace AlgebraicGeometry.GroupoidsOver.LQCohFbc

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable {A : AlgebraicSpace S} (f : A.toGroupoids ⟶ X)

/-- The actual étale inverse image of a module along a test algebraic space. -/
private def inverseImage (F : LQCohFbc X) : etaleModules A.toGroupoids :=
  (etaleModuleInverseImage f).obj F.obj

/-- The small-étale scheme restriction on a test chart, transported to its
represented algebraic space by recovered-chart extension. -/
private def chartModule (F : LQCohFbc X) (U : smallEtaleSite A) :
    Modules (ofOver U.left) :=
  (SchemeEtaleModules.fromScheme U.left).obj
    ((restrictModulesToSmallEtale A.toGroupoids (toGroupoidsObj U)).obj (inverseImage f F))

/-- The chart transition uses the actual scheme module comparison and the
represented-scheme pullback comparison. -/
private def chartTransitionHom (F : LQCohFbc X) {U V : smallEtaleSite A} (a : V ⟶ U) :
    (SmallEtaleModuleGlueing.pullback a).obj (chartModule f F U) ⟶ chartModule f F V :=
  (SchemeEtaleModules.pullbackIso a.left).hom.app
      ((restrictModulesToSmallEtale A.toGroupoids (toGroupoidsObj U)).obj (inverseImage f F)) ≫
    (SchemeEtaleModules.fromScheme V.left).map
      (moduleComparison (toGroupoidsMap a) (inverseImage f F))

/-- Invertible chart comparisons give the chart transition isomorphisms. -/
private def chartTransition (F : LQCohFbc X)
    (hi : ∀ {U V : smallEtaleSite A} (a : V ⟶ U), IsIso (chartTransitionHom f F a))
    {U V : smallEtaleSite A} (a : V ⟶ U) :
    (SmallEtaleModuleGlueing.pullback a).obj (chartModule f F U) ≅ chartModule f F V :=
  @asIso _ _ _ _ (chartTransitionHom f F a) (hi a)

/-- Flat base change makes the chart comparisons invertible, and the
canonical comparison coherences give their identity and cocycle laws. -/
private theorem restrictSpaceTransitions_laws (F : LQCohFbc X) :
    (∀ {U V : smallEtaleSite A} (a : V ⟶ U), IsIso (chartTransitionHom f F a)) ∧
    ∀ hi : ∀ {U V : smallEtaleSite A} (a : V ⟶ U), IsIso (chartTransitionHom f F a),
      (∀ U : smallEtaleSite A,
        chartTransition f F hi (𝟙 U) = (SmallEtaleModuleGlueing.pullbackId U).app (chartModule f F U)) ∧
      (∀ {U V W : smallEtaleSite A} (a : V ⟶ U) (b : W ⟶ V),
        (SmallEtaleModuleGlueing.pullbackComp a b).app (chartModule f F U) ≪≫
            chartTransition f F hi (b ≫ a) =
          (SmallEtaleModuleGlueing.pullback b).mapIso (chartTransition f F hi a) ≪≫
            chartTransition f F hi b) := sorry

/-- The compatible small-étale chart system associated to a test algebraic space. -/
private def restrictionSystem (F : LQCohFbc X) : SmallEtaleModuleGlueing.Object A where
  obj := chartModule f F
  transition := chartTransition f F (restrictSpaceTransitions_laws f F).1
  transition_id := ((restrictSpaceTransitions_laws f F).2 (restrictSpaceTransitions_laws f F).1).1
  transition_comp := ((restrictSpaceTransitions_laws f F).2 (restrictSpaceTransitions_laws f F).1).2

/-- A module morphism acts on a test chart by inverse image, scheme
restriction, and recovered-chart extension. -/
private def chartMap {F G : LQCohFbc X} (φ : F ⟶ G) (U : smallEtaleSite A) :
    chartModule f F U ⟶ chartModule f G U :=
  (SchemeEtaleModules.fromScheme U.left).map
    ((restrictModulesToSmallEtale A.toGroupoids (toGroupoidsObj U)).map
      ((etaleModuleInverseImage f).map φ.hom))

/-- Chart maps commute with the transported flat-base-change transitions. -/
private def chartMapNaturality : Prop :=
  ∀ {F G : LQCohFbc X} (φ : F ⟶ G) {U V : smallEtaleSite A} (a : V ⟶ U),
    CommSq ((SmallEtaleModuleGlueing.pullback a).map (chartMap f φ U))
      ((restrictionSystem f F).transition a).hom
      ((restrictionSystem f G).transition a).hom (chartMap f φ V)

/-- Compatible chart maps form a morphism of chart systems. -/
private def systemMap (hn : chartMapNaturality f) {F G : LQCohFbc X} (φ : F ⟶ G) :
    SmallEtaleModuleGlueing.Hom (restrictionSystem f F) (restrictionSystem f G) where
  app := chartMap f φ
  naturality := hn φ

/-- Chart maps are natural and preserve identities and composition. -/
private theorem restrictSpaceMap_laws :
    chartMapNaturality f ∧ ∀ hn : chartMapNaturality f,
      (∀ F : LQCohFbc X, systemMap f hn (𝟙 F) = SmallEtaleModuleGlueing.Hom.id _) ∧
      (∀ {F G H : LQCohFbc X} (φ : F ⟶ G) (ψ : G ⟶ H),
        systemMap f hn (φ ≫ ψ) =
          SmallEtaleModuleGlueing.Hom.comp (systemMap f hn φ) (systemMap f hn ψ)) := sorry

/-- Chart restriction is a functor into the explicit category of compatible systems. -/
private def restrictionSystems : LQCohFbc X ⥤ SmallEtaleModuleGlueing.category A where
  obj := restrictionSystem f
  map := systemMap f (restrictSpaceMap_laws f).1
  map_id := ((restrictSpaceMap_laws f).2 (restrictSpaceMap_laws f).1).1
  map_comp := ((restrictSpaceMap_laws f).2 (restrictSpaceMap_laws f).1).2

/-- Restriction to a test algebraic space, reconstructed from transported
small-étale scheme restrictions and their flat-base-change transitions. -/
def restrictSpaceFunctor : LQCohFbc X ⥤ Modules A :=
  restrictionSystems f ⋙ SmallEtaleModuleGlueing.toModules A

/-- Restriction of a locally quasi-coherent flat-base-change module to a
test algebraic space is quasi-coherent. -/
theorem restrictSpaceQuasicoherent (F : LQCohFbc X) :
    ((restrictSpaceFunctor f).obj F).IsQuasicoherent := sorry

/-- Quasi-coherent restriction to a test algebraic space. -/
def restrictSpace : LQCohFbc X ⥤ AlgebraicSpace.QCoh A :=
  (AlgebraicSpace.quasiCoherentModuleProperty A).lift (restrictSpaceFunctor f)
    (restrictSpaceQuasicoherent f)

/-- The recovered scheme chart underlying the identity chart of a represented scheme. -/
private def identityChart (U : smallEtaleSite A) : U.left.left.Etale :=
  (SchemeEtaleModules.siteInverse U.left).obj (SmallEtaleGlueing.idObj U.left)

/-- Cartesian evaluation at the recovered identity chart maps to the original test object. -/
private def identityEvaluationArrow (U : smallEtaleSite A) :=
  smallEtaleEval_toBase (toGroupoidsObj U) (identityChart U)

/-- Direct restriction evaluates a module on the objects of the test space's
small étale site, with the canonical coefficient maps. -/
private def directRestriction : LQCohFbc X ⥤ Modules A :=
  LQCohFbc.inclusion X ⋙ etaleModuleInverseImage f ⋙
    (pi A A.toGroupoids (Bicategory.Equivalence.id _)).modulePushforward.{u}

/-- Recovered-chart evaluation followed by the inverse identity-cartesian
restriction is an additive equivalence of section modules. -/
private def sectionEvaluation (hi : ∀ U : smallEtaleSite A, IsIso (identityEvaluationArrow U))
    (F : LQCohFbc X) (U : (smallEtaleSite A)ᵒᵖ) :
    ((restrictSpaceFunctor f).obj F).val.obj U ≃+
      ((directRestriction f).obj F).val.obj U :=
  ((SchemeEtaleModules.evaluation U.unop.left
      ((restrictModulesToSmallEtale A.toGroupoids (toGroupoidsObj U.unop)).obj
        (inverseImage f F)) (SmallEtaleGlueing.idObj U.unop.left)).toLinearEquiv.toAddEquiv.trans
      (((SheafOfModules.evaluation
        (Scheme.Etale.Small.structureSheaf U.unop.left.left)
        (op (identityChart U.unop))).mapIso
          (restrictEtaleIso (inverseImage f F) (toGroupoidsObj U.unop))).toLinearEquiv.toAddEquiv)).trans
    (((inverseImage f F).val.presheaf.mapIso
      (@asIso _ _ _ _ (identityEvaluationArrow U.unop) (hi U.unop)).op).symm.addCommGroupIsoToAddEquiv)

/-- Linearity of identity-chart evaluation with the actual coefficient maps. -/
private def evaluationLinearity
    (hi : ∀ U : smallEtaleSite A, IsIso (identityEvaluationArrow U)) : Prop :=
  ∀ (F : LQCohFbc X) (U : (smallEtaleSite A)ᵒᵖ)
    (r : (AlgebraicSpace.structureSheaf A).obj.obj U) (s : ((restrictSpaceFunctor f).obj F).val.obj U),
      sectionEvaluation f hi F U (r • s) = r • sectionEvaluation f hi F U s

set_option maxHeartbeats 1600000 in
/-- Identity-chart evaluation as a linear isomorphism. -/
private def evaluationComponent
    (hi : ∀ U : smallEtaleSite A, IsIso (identityEvaluationArrow U))
    (hl : evaluationLinearity f hi) (F : LQCohFbc X) (U : (smallEtaleSite A)ᵒᵖ) :
    ((restrictSpaceFunctor f).obj F).val.obj U ≅ ((directRestriction f).obj F).val.obj U :=
  ((sectionEvaluation f hi F U).toLinearEquiv (hl F U)).toModuleIso

set_option maxHeartbeats 1600000 in
/-- Identity-chart evaluation commutes with restriction of sections. -/
private def evaluationNaturality
    (hi : ∀ U : smallEtaleSite A, IsIso (identityEvaluationArrow U))
    (hl : evaluationLinearity f hi) : Prop :=
  ∀ (F : LQCohFbc X) {U V : (smallEtaleSite A)ᵒᵖ} (a : U ⟶ V),
    ((restrictSpaceFunctor f).obj F).val.map a ≫
      (ModuleCat.restrictScalars ((AlgebraicSpace.structureSheaf A).obj.map a).hom).map
        (evaluationComponent f hi hl F V).hom =
      (evaluationComponent f hi hl F U).hom ≫ ((directRestriction f).obj F).val.map a

set_option maxHeartbeats 1600000 in
/-- Recovered-chart evaluation gives an isomorphism of the reconstructed and
directly evaluated module sheaves. -/
private def evaluationModuleIso
    (hi : ∀ U : smallEtaleSite A, IsIso (identityEvaluationArrow U))
    (hl : evaluationLinearity f hi) (hn : evaluationNaturality f hi hl) (F : LQCohFbc X) :
    (restrictSpaceFunctor f).obj F ≅ (directRestriction f).obj F :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (evaluationComponent f hi hl F) (fun {_ _} a ↦ hn F a))

set_option maxHeartbeats 1600000 in
/-- Identity-cartesian arrows are invertible, and recovered-chart evaluation
is linear and natural in both charts and modules. -/
private theorem restrictSpaceEvaluation_laws :
    (∀ U : smallEtaleSite A, IsIso (identityEvaluationArrow U)) ∧
    ∀ hi : ∀ U : smallEtaleSite A, IsIso (identityEvaluationArrow U),
      evaluationLinearity f hi ∧ ∀ hl : evaluationLinearity f hi,
        evaluationNaturality f hi hl ∧ ∀ hn : evaluationNaturality f hi hl,
          ∀ {F G : LQCohFbc X} (φ : F ⟶ G),
            (restrictSpaceFunctor f).map φ ≫ (evaluationModuleIso f hi hl hn G).hom =
              (evaluationModuleIso f hi hl hn F).hom ≫ (directRestriction f).map φ := sorry

set_option maxHeartbeats 1600000 in
/-- Evaluation of the glued restriction agrees with actual étale inverse
image followed by restriction to the algebraic space's small étale charts. -/
def restrictSpaceEvaluation : restrictSpaceFunctor f ≅ directRestriction f :=
  let hi := (restrictSpaceEvaluation_laws f).1
  let hl := ((restrictSpaceEvaluation_laws f).2 hi).1
  let hn := (((restrictSpaceEvaluation_laws f).2 hi).2 hl).1
  NatIso.ofComponents (evaluationModuleIso f hi hl hn)
    (fun {_ _} a ↦ (((restrictSpaceEvaluation_laws f).2 hi).2 hl).2 hn a)

open CategoryTheory.Limits CategoryTheory.Sheaf.InternalModule

variable {B : AlgebraicSpace S} (h : A ⟶ B) (g : B.toGroupoids ⟶ X)

set_option maxHeartbeats 1600000 in
/-- The target chart arrow induced by a chart over its inverse image has
its prescribed Yoneda endpoint. -/
private def squareEndpoints : Prop :=
  ∀ (V : smallEtaleSite B)
    (a : StructuredArrow (op ((etaleBaseChange h).obj V))
      (SpacesEtale.AtlasCharts.inclusion A).op),
    B.functorOfPoints.map (EtaleRingedTopos.schemeMap h V a).op (yonedaSection V.hom) =
      h.app (op (SmallEtale.AtlasCharts.object A a.right.unop).left)
        (yonedaSection (SmallEtale.AtlasCharts.object A a.right.unop).hom)

set_option maxHeartbeats 1600000 in
/-- A scheme chart of an inverse image determines its actual target-groupoid arrow. -/
private def squareArrow (he : squareEndpoints h) (V : smallEtaleSite B)
    (a : StructuredArrow (op ((etaleBaseChange h).obj V))
      (SpacesEtale.AtlasCharts.inclusion A).op) :
    (toFunctor (toGroupoids.map h)).obj
        (toGroupoidsObj (SmallEtale.AtlasCharts.object A a.right.unop)) ⟶ toGroupoidsObj V :=
  Quiver.Hom.op (CategoryOfElements.homMk _ _
    (EtaleRingedTopos.schemeMap h V a).op (he V a))

set_option maxHeartbeats 1600000 in
/-- Restricting along the actual target-groupoid arrow gives the section
component on a scheme chart of an inverse image. -/
private def squareSection (he : squareEndpoints h) (F : LQCohFbc X) (V : smallEtaleSite B)
    (a : StructuredArrow (op ((etaleBaseChange h).obj V))
      (SpacesEtale.AtlasCharts.inclusion A).op) :
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf B)).obj ((directRestriction g).obj F)).obj.obj (op V) →
      (((EtaleTopos.smallEquivalence A).functor.obj
        ((ToInternal.underlying (AlgebraicSpace.structureSheaf A)).obj
          ((directRestriction (toGroupoids.map h ≫ g)).obj F))).obj.obj a.right) :=
  fun s ↦ (ToInternal.sectionEquiv (AlgebraicSpace.structureSheaf A)
      ((directRestriction (toGroupoids.map h ≫ g)).obj F)
      (op (SmallEtale.AtlasCharts.object A a.right.unop))).symm
    (F.obj.val.map ((toFunctor g).map (squareArrow h he V a)).op
      (ToInternal.sectionEquiv (AlgebraicSpace.structureSheaf B) ((directRestriction g).obj F) (op V) s))

set_option maxHeartbeats 1600000 in
/-- The section restrictions on inverse-image charts form a cone. -/
private def squareConeNaturality (he : squareEndpoints h) : Prop :=
  ∀ (F : LQCohFbc X) (V : smallEtaleSite B)
    {a b : StructuredArrow (op ((etaleBaseChange h).obj V))
      (SpacesEtale.AtlasCharts.inclusion A).op} (k : a ⟶ b),
    (TypeCat.ofHom (squareSection h g he F V a)) ≫
      (StructuredArrow.proj (op ((etaleBaseChange h).obj V))
        (SpacesEtale.AtlasCharts.inclusion A).op ⋙
        ((EtaleTopos.smallEquivalence A).functor.obj
          ((ToInternal.underlying (AlgebraicSpace.structureSheaf A)).obj
            ((directRestriction (toGroupoids.map h ≫ g)).obj F))).obj).map k =
      TypeCat.ofHom (squareSection h g he F V b)

set_option maxHeartbeats 1600000 in
/-- The actual cone of target-section restrictions on inverse-image charts. -/
private def squareCone (he : squareEndpoints h) (hn : squareConeNaturality h g he)
    (F : LQCohFbc X) (V : smallEtaleSite B) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange h).obj V))
      (SpacesEtale.AtlasCharts.inclusion A).op ⋙
        ((EtaleTopos.smallEquivalence A).functor.obj
          ((ToInternal.underlying (AlgebraicSpace.structureSheaf A)).obj
            ((directRestriction (toGroupoids.map h ≫ g)).obj F))).obj) where
  pt := ((ToInternal.underlying (AlgebraicSpace.structureSheaf B)).obj ((directRestriction g).obj F)).obj.obj (op V)
  π := { app := fun a ↦ TypeCat.ofHom (squareSection h g he F V a), naturality := fun {_ _} a ↦ (Category.id_comp _).trans (hn F V a).symm }

set_option maxHeartbeats 1600000 in
/-- The direct-image section comparison is the actual right-Kan limit lift. -/
private def squareMapApp (he : squareEndpoints h) (hn : squareConeNaturality h g he)
    (F : LQCohFbc X) (V : (smallEtaleSite B)ᵒᵖ) :
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf B)).obj ((directRestriction g).obj F)).obj.obj V ⟶
      ((EtaleTopos.directImage h).obj
        ((ToInternal.underlying (AlgebraicSpace.structureSheaf A)).obj
          ((directRestriction (toGroupoids.map h ≫ g)).obj F))).obj.obj V :=
  limit.lift _ (squareCone h g he hn F V.unop) ≫
    ((SpacesEtale.AtlasCharts.inclusion A).op.ranObjObjIsoLimit
      ((EtaleTopos.smallEquivalence A).functor.obj
        ((ToInternal.underlying (AlgebraicSpace.structureSheaf A)).obj
          ((directRestriction (toGroupoids.map h ≫ g)).obj F))).obj
      (op ((etaleBaseChange h).obj V.unop))).inv

set_option maxHeartbeats 1600000 in
/-- The right-Kan section comparison is natural in target charts. -/
private def squareMapNaturality (he : squareEndpoints h) (hn : squareConeNaturality h g he) : Prop :=
  ∀ (F : LQCohFbc X) {V W : (smallEtaleSite B)ᵒᵖ} (a : V ⟶ W),
    ((ToInternal.underlying (AlgebraicSpace.structureSheaf B)).obj ((directRestriction g).obj F)).obj.map a ≫
        squareMapApp h g he hn F W =
      squareMapApp h g he hn F V ≫
        ((EtaleTopos.directImage h).obj
          ((ToInternal.underlying (AlgebraicSpace.structureSheaf A)).obj
            ((directRestriction (toGroupoids.map h ≫ g)).obj F))).obj.map a

set_option maxHeartbeats 1600000 in
/-- The actual comparison of underlying sheaves, with the canonical
module-direct-image forgetful identification. -/
private def squareUnderlying (he : squareEndpoints h) (hn : squareConeNaturality h g he)
    (hm : squareMapNaturality h g he hn) (F : LQCohFbc X) :
    (ToInternal.underlying (AlgebraicSpace.structureSheaf B)).obj ((directRestriction g).obj F) ⟶
      (ToInternal.underlying (AlgebraicSpace.structureSheaf B)).obj
        ((Modules.pushforward h).obj ((directRestriction (toGroupoids.map h ≫ g)).obj F)) :=
  ObjectProperty.homMk
    { app := squareMapApp h g he hn F, naturality := fun {_ _} a ↦ hm F a } ≫
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom h)).inv.app
        ((directRestriction (toGroupoids.map h ≫ g)).obj F)

set_option maxHeartbeats 1600000 in
/-- The actual right-Kan comparison respects addition and scalar restriction. -/
private def squareLinearity (he : squareEndpoints h) (hn : squareConeNaturality h g he)
    (hm : squareMapNaturality h g he hn) : Prop :=
  ∀ F : LQCohFbc X,
    (∀ U (s t : ((directRestriction g).obj F).val.obj U),
      underlyingApp (AlgebraicSpace.structureSheaf B) (squareUnderlying h g he hn hm F) U (s + t) =
        underlyingApp (AlgebraicSpace.structureSheaf B) (squareUnderlying h g he hn hm F) U s +
          underlyingApp (AlgebraicSpace.structureSheaf B) (squareUnderlying h g he hn hm F) U t) ∧
    (∀ U (r : (AlgebraicSpace.structureSheaf B).obj.obj U) (s : ((directRestriction g).obj F).val.obj U),
      underlyingApp (AlgebraicSpace.structureSheaf B) (squareUnderlying h g he hn hm F) U (r • s) =
        r • underlyingApp (AlgebraicSpace.structureSheaf B) (squareUnderlying h g he hn hm F) U s)

set_option maxHeartbeats 1600000 in
/-- The actual pullback comparison is the adjunct of chartwise restrictions
into the explicit small-chart direct image. -/
private def directComparison (he : squareEndpoints h) (hn : squareConeNaturality h g he)
    (hm : squareMapNaturality h g he hn) (hl : squareLinearity h g he hn hm)
    (F : LQCohFbc X) :
    (Modules.pullback h).obj ((directRestriction g).obj F) ⟶
      (directRestriction (toGroupoids.map h ≫ g)).obj F :=
  Modules.adjointToPushforward h
    (homOfUnderlying (AlgebraicSpace.structureSheaf B) (squareUnderlying h g he hn hm F)
      (hl F).1 (hl F).2)

set_option maxHeartbeats 1600000 in
/-- Chartwise restrictions give an additive, coefficient-compatible cone,
and their adjoint comparison is natural and invertible for a flat morphism. -/
private theorem restrictionComparison_laws :
    squareEndpoints h ∧ ∀ he : squareEndpoints h,
      squareConeNaturality h g he ∧ ∀ hn : squareConeNaturality h g he,
        squareMapNaturality h g he hn ∧ ∀ hm : squareMapNaturality h g he hn,
          squareLinearity h g he hn hm ∧ ∀ hl : squareLinearity h g he hn hm,
            (∀ {F G : LQCohFbc X} (φ : F ⟶ G),
              (Modules.pullback h).map ((directRestriction g).map φ) ≫
                  directComparison h g he hn hm hl G =
                directComparison h g he hn hm hl F ≫
                  (directRestriction (toGroupoids.map h ≫ g)).map φ) ∧
            (AlgebraicSpace.Flat h → ∀ F : LQCohFbc X,
              IsIso (directComparison h g he hn hm hl F)) := sorry

set_option maxHeartbeats 1600000 in
/-- The direct restriction comparison is natural in locally quasi-coherent
modules with flat base change. -/
private def directComparisonNat :
    directRestriction g ⋙ Modules.pullback h ⟶ directRestriction (toGroupoids.map h ≫ g) :=
  let he := (restrictionComparison_laws h g).1
  let hn := ((restrictionComparison_laws h g).2 he).1
  let hm := (((restrictionComparison_laws h g).2 he).2 hn).1
  let hl := ((((restrictionComparison_laws h g).2 he).2 hn).2 hm).1
  { app := directComparison h g he hn hm hl
    naturality := fun {_ _} a ↦ (((((restrictionComparison_laws h g).2 he).2 hn).2 hm).2 hl).1 a }

set_option maxHeartbeats 1600000 in
/-- Flat pullback of the restriction to a test space is canonically
isomorphic to restriction along the composite test morphism. -/
def restrictionComparison (hh : AlgebraicSpace.Flat h) :
    restrictSpaceFunctor g ⋙ Modules.pullback h ≅
      restrictSpaceFunctor (toGroupoids.map h ≫ g) :=
  let he := (restrictionComparison_laws h g).1
  let hn := ((restrictionComparison_laws h g).2 he).1
  let hm := (((restrictionComparison_laws h g).2 he).2 hn).1
  let hl := ((((restrictionComparison_laws h g).2 he).2 hn).2 hm).1
  let hi := (((((restrictionComparison_laws h g).2 he).2 hn).2 hm).2 hl).2 hh
  Functor.isoWhiskerRight (restrictSpaceEvaluation g) (Modules.pullback h) ≪≫
    NatIso.ofComponents (fun F ↦ @asIso _ _ _ _ (directComparison h g he hn hm hl F) (hi F))
      (fun {_ _} a ↦ (((((restrictionComparison_laws h g).2 he).2 hn).2 hm).2 hl).1 a) ≪≫
    (restrictSpaceEvaluation (toGroupoids.map h ≫ g)).symm

variable {f₁ f₂ : A.toGroupoids ⟶ X}

/-- A test-morphism isomorphism acts on sections through its inverse
component in the original module sheaf. -/
private def cellFunction (e : f₁ ≅ f₂) (F : LQCohFbc X) (U : (smallEtaleSite A)ᵒᵖ) :
    ((directRestriction f₁).obj F).val.obj U → ((directRestriction f₂).obj F).val.obj U :=
  fun s ↦ F.obj.val.map ((toNatTrans e.inv).app (toGroupoidsObj U.unop)).op s

/-- Vertical section maps are additive and compatible with the test-space scalars. -/
private def cellLinearity (e : f₁ ≅ f₂) : Prop :=
  ∀ (F : LQCohFbc X) (U : (smallEtaleSite A)ᵒᵖ),
    (∀ s t, cellFunction e F U (s + t) = cellFunction e F U s + cellFunction e F U t) ∧
    (∀ (r : (AlgebraicSpace.structureSheaf A).obj.obj U) s,
      cellFunction e F U (r • s) = r • cellFunction e F U s)

/-- The actual section map of a vertical test isomorphism as a linear morphism. -/
private def cellComponent (e : f₁ ≅ f₂) (hl : cellLinearity e)
    (F : LQCohFbc X) (U : (smallEtaleSite A)ᵒᵖ) :
    ((directRestriction f₁).obj F).val.obj U ⟶ ((directRestriction f₂).obj F).val.obj U :=
  ModuleCat.ofHom (X := ((directRestriction f₁).obj F).val.obj U)
    (Y := ((directRestriction f₂).obj F).val.obj U)
    { toFun := cellFunction e F U
      map_add' := (hl F U).1
      map_smul' := (hl F U).2 }

/-- The section map of a vertical test isomorphism commutes with restriction. -/
private def cellNaturality (e : f₁ ≅ f₂) (hl : cellLinearity e) : Prop :=
  ∀ (F : LQCohFbc X) {U V : (smallEtaleSite A)ᵒᵖ} (a : U ⟶ V),
    ((directRestriction f₁).obj F).val.map a ≫
        (ModuleCat.restrictScalars ((AlgebraicSpace.structureSheaf A).obj.map a).hom).map
          (cellComponent e hl F V) =
      cellComponent e hl F U ≫ ((directRestriction f₂).obj F).val.map a

/-- The original vertical restrictions define a morphism of module sheaves. -/
private def cellMap (e : f₁ ≅ f₂) (hl : cellLinearity e) (hn : cellNaturality e hl)
    (F : LQCohFbc X) : (directRestriction f₁).obj F ⟶ (directRestriction f₂).obj F where
  val := { app := cellComponent e hl F, naturality := fun {_ _} a ↦ hn F a }

set_option maxHeartbeats 1600000 in
/-- Test-morphism isomorphisms induce inverse, natural, coefficient-compatible
module maps through their actual vertical components. -/
private theorem restrictionIso_laws (e : f₁ ≅ f₂) :
    (cellLinearity e ∧ cellLinearity e.symm) ∧
    ∀ (hl : cellLinearity e) (hr : cellLinearity e.symm),
      (cellNaturality e hl ∧ cellNaturality e.symm hr) ∧
      ∀ (hn : cellNaturality e hl) (hm : cellNaturality e.symm hr),
        (∀ F : LQCohFbc X,
          (cellMap e hl hn F ≫ cellMap e.symm hr hm F = 𝟙 _) ∧
          (cellMap e.symm hr hm F ≫ cellMap e hl hn F = 𝟙 _)) ∧
        (∀ {F G : LQCohFbc X} (φ : F ⟶ G),
          (directRestriction f₁).map φ ≫ cellMap e hl hn G =
            cellMap e hl hn F ≫ (directRestriction f₂).map φ) := sorry

/-- Restriction to algebraic spaces respects isomorphisms of their test
morphisms, using the original sheaf's vertical restriction maps. -/
def restrictionIso (e : f₁ ≅ f₂) : restrictSpaceFunctor f₁ ≅ restrictSpaceFunctor f₂ :=
  let hl := (restrictionIso_laws e).1.1
  let hr := (restrictionIso_laws e).1.2
  let hn := ((restrictionIso_laws e).2 hl hr).1.1
  let hm := ((restrictionIso_laws e).2 hl hr).1.2
  let laws := ((restrictionIso_laws e).2 hl hr).2 hn hm
  restrictSpaceEvaluation f₁ ≪≫
    NatIso.ofComponents (fun F ↦
      { hom := cellMap e hl hn F
        inv := cellMap e.symm hr hm F
        hom_inv_id := (laws.1 F).1
        inv_hom_id := (laws.1 F).2 }) (fun {_ _} a ↦ laws.2 a) ≪≫
    (restrictSpaceEvaluation f₂).symm

end AlgebraicGeometry.GroupoidsOver.LQCohFbc
