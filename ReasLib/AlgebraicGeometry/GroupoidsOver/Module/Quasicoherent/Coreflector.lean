/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ChosenPresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Presentation.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Reconstruction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.SpaceRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.Flat

/-! # The quasi-coherent coreflector for modules with flat base change -/

@[expose] public section
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry Opposite
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidAlgebraicSpace AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

noncomputable section
universe u
namespace AlgebraicGeometry.GroupoidsOver
variable {S : Scheme.{u}}

/-- Restriction of a quasi-coherent fppf module is locally quasi-coherent
and has flat base change on the étale site. -/
theorem QCoh.toLQCohFbc_mapsTo (X : GroupoidsOver S) [AlgebraicStack X] (F : QCoh X) :
    lqcohFbc X ((QCoh.inclusion X ⋙ restriction X).obj F) := sorry

/-- The inclusion of quasi-coherent modules into locally quasi-coherent
étale modules with flat base change is the actual topology restriction. -/
def QCoh.toLQCohFbc (X : GroupoidsOver S) [AlgebraicStack X] : QCoh X ⥤ LQCohFbc X :=
  (lqcohFbc X).lift (QCoh.inclusion X ⋙ restriction X) (QCoh.toLQCohFbc_mapsTo X)

/-- Forgetting the flat-base-change property of a restricted quasi-coherent
module recovers topology restriction. -/
theorem QCoh.toLQCohFbc_comp_inclusion (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh.toLQCohFbc X ⋙ LQCohFbc.inclusion X = QCoh.inclusion X ⋙ restriction X := rfl

/-- Topology restriction of quasi-coherent modules is full. -/
instance QCoh.toLQCohFbc_full (X : GroupoidsOver S) [AlgebraicStack X] :
    (QCoh.toLQCohFbc X).Full := sorry

/-- Topology restriction of quasi-coherent modules is faithful. -/
instance QCoh.toLQCohFbc_faithful (X : GroupoidsOver S) [AlgebraicStack X] :
    (QCoh.toLQCohFbc X).Faithful := sorry

/-- The morphism from the presentation object space to the stack. -/
private def atlasMorphism (X : GroupoidsOver S) [AlgebraicStack X] :
    (algebraicStackPresentation X).groupoid.U.left.toGroupoids ⟶ X :=
  SmallQuotient.atlas (algebraicStackPresentation X).groupoid ≫ (algebraicStackPresentation X).hom

/-- Restriction to the object space of a smooth presentation. -/
def LQCohFbc.atlasRestrict (X : GroupoidsOver S) [AlgebraicStack X] (F : LQCohFbc X) :
    AlgebraicSpace.QCoh (algebraicStackPresentation X).groupoid.U.left :=
  (LQCohFbc.restrictSpace (atlasMorphism X)).obj F

/-- The universal relation point identifies the source and target test morphisms. -/
private def atlasCell (X : GroupoidsOver S) [AlgebraicStack X] :
    AlgebraicSpace.toGroupoids.map (algebraicStackPresentation X).groupoid.s.left ≫ atlasMorphism X ≅
      AlgebraicSpace.toGroupoids.map (algebraicStackPresentation X).groupoid.t.left ≫ atlasMorphism X :=
  let P := algebraicStackPresentation X
  (α_ (AlgebraicSpace.toGroupoids.map P.groupoid.s.left) (SmallQuotient.atlas P.groupoid) P.hom).symm ≪≫
    Bicategory.whiskerRightIso (SmallQuotient.sourceTargetIso P.groupoid) P.hom ≪≫
    α_ (AlgebraicSpace.toGroupoids.map P.groupoid.t.left) (SmallQuotient.atlas P.groupoid) P.hom

/-- The descent action is target flat comparison, the universal groupoid
cell, and inverse source flat comparison, in direction `t^*F ⟶ s^*F`. -/
def LQCohFbc.atlasAction (X : GroupoidsOver S) [AlgebraicStack X] (F : LQCohFbc X) :
    (AlgebraicSpace.QCoh.pullback (algebraicStackPresentation X).groupoid.t.left).obj
        (LQCohFbc.atlasRestrict X F) ⟶
      (AlgebraicSpace.QCoh.pullback (algebraicStackPresentation X).groupoid.s.left).obj
        (LQCohFbc.atlasRestrict X F) :=
  let P := algebraicStackPresentation X
  ObjectProperty.homMk
    ((LQCohFbc.restrictionComparison P.groupoid.t.left (atlasMorphism X)
        (@AlgebraicSpace.Smooth.flat _ _ _ P.groupoid.t.left (Smooth.target P.isSmooth))).hom.app F ≫
      (LQCohFbc.restrictionIso (atlasCell X)).inv.app F ≫
      (LQCohFbc.restrictionComparison P.groupoid.s.left (atlasMorphism X)
        (@AlgebraicSpace.Smooth.flat _ _ _ P.groupoid.s.left (Smooth.source P.isSmooth))).inv.app F)

/-- The descent action induced by the universal relation satisfies the
cocycle and identity-section conditions. -/
private theorem LQCohFbc.atlasAction_laws (X : GroupoidsOver S) [AlgebraicStack X]
    (F : LQCohFbc X) :
    Cocycle (algebraicStackPresentation X).groupoid (LQCohFbc.atlasRestrict X F)
        (LQCohFbc.atlasAction X F) ∧
      Unit (algebraicStackPresentation X).groupoid (LQCohFbc.atlasRestrict X F)
        (LQCohFbc.atlasAction X F) := sorry

/-- The equivariant module obtained by restriction to a smooth presentation. -/
private def descentObj (X : GroupoidsOver S) [AlgebraicStack X] (F : LQCohFbc X) :
    (algebraicStackPresentation X).groupoid.QCoh :=
  GroupoidAlgebraicSpace.QCoh.of (LQCohFbc.atlasRestrict X F) (LQCohFbc.atlasAction X F)
    (LQCohFbc.atlasAction_laws X F).1 (LQCohFbc.atlasAction_laws X F).2

/-- Restriction of module morphisms to a presentation respects descent actions. -/
private def descentMapCompatibility (X : GroupoidsOver S) [AlgebraicStack X] : Prop :=
  ∀ {F G : LQCohFbc X} (φ : F ⟶ G),
    (AlgebraicSpace.QCoh.pullback (algebraicStackPresentation X).groupoid.t.left).map
        ((LQCohFbc.restrictSpace (atlasMorphism X)).map φ) ≫ LQCohFbc.atlasAction X G =
      LQCohFbc.atlasAction X F ≫
        (AlgebraicSpace.QCoh.pullback (algebraicStackPresentation X).groupoid.s.left).map
          ((LQCohFbc.restrictSpace (atlasMorphism X)).map φ)

/-- The descent morphism retains the actual restricted module map. -/
private def descentMap (X : GroupoidsOver S) [AlgebraicStack X]
    (hc : descentMapCompatibility X) {F G : LQCohFbc X} (φ : F ⟶ G) :
    descentObj X F ⟶ descentObj X G :=
  System.Hom.of ((LQCohFbc.restrictSpace (atlasMorphism X)).map φ) (hc φ)

/-- Descent of module morphisms is equivariant and preserves identities and composition. -/
private theorem LQCohFbc.toGroupoidModules_laws (X : GroupoidsOver S) [AlgebraicStack X] :
    descentMapCompatibility X ∧ ∀ hc : descentMapCompatibility X,
      (∀ F : LQCohFbc X, descentMap X hc (𝟙 F) = 𝟙 _) ∧
      (∀ {F G H : LQCohFbc X} (φ : F ⟶ G) (ψ : G ⟶ H),
        descentMap X hc (φ ≫ ψ) = descentMap X hc φ ≫ descentMap X hc ψ) := sorry

/-- Descent sends a flat-base-change module to its actual atlas restriction
with the universal groupoid action. -/
def LQCohFbc.toGroupoidModules (X : GroupoidsOver S) [AlgebraicStack X] :
    LQCohFbc X ⥤ (algebraicStackPresentation X).groupoid.QCoh where
  obj := descentObj X
  map := descentMap X (LQCohFbc.toGroupoidModules_laws X).1
  map_id := ((LQCohFbc.toGroupoidModules_laws X).2 (LQCohFbc.toGroupoidModules_laws X).1).1
  map_comp := ((LQCohFbc.toGroupoidModules_laws X).2 (LQCohFbc.toGroupoidModules_laws X).1).2

/-- The underlying module of descent is the atlas restriction. -/
theorem LQCohFbc.toGroupoidModules_obj (X : GroupoidsOver S) [AlgebraicStack X] (F : LQCohFbc X) :
    GroupoidAlgebraicSpace.QCoh.obj ((LQCohFbc.toGroupoidModules X).obj F) =
      LQCohFbc.atlasRestrict X F := rfl

/-- The equivariance map of descent is the universal groupoid action. -/
theorem LQCohFbc.toGroupoidModules_action (X : GroupoidsOver S) [AlgebraicStack X] (F : LQCohFbc X) :
    GroupoidAlgebraicSpace.QCoh.action ((LQCohFbc.toGroupoidModules X).obj F) =
      LQCohFbc.atlasAction X F := rfl

/-- Quasi-coherent reconstruction from a presentation, with inverse
presentation pullback supplied by actual compatible-section extension. -/
private def presentationReconstruction (X : GroupoidsOver S) [AlgebraicStack X] :
    (algebraicStackPresentation X).groupoid.QCoh ⥤ QCoh X :=
  QuotientQCoh.fromGroupoidStack (algebraicStackPresentation X).groupoid ⋙
    (Presentation.qcohEquivalence (algebraicStackPresentation X)).inverse

/-- The quasi-coherent coreflector is actual presentation descent followed
by quotient reconstruction and inverse presentation pullback. -/
def LQCohFbc.toQCoh (X : GroupoidsOver S) [AlgebraicStack X] : LQCohFbc X ⥤ QCoh X :=
  LQCohFbc.toGroupoidModules X ⋙ presentationReconstruction X

/-- The coreflector is the composite of presentation descent and reconstruction. -/
theorem LQCohFbc.toQCoh_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    LQCohFbc.toQCoh X = LQCohFbc.toGroupoidModules X ⋙
      QuotientQCoh.fromGroupoidStack (algebraicStackPresentation X).groupoid ⋙
        (Presentation.qcohEquivalence (algebraicStackPresentation X)).inverse := sorry

/-- Restriction of quasi-coherent modules to the chosen presentation groupoid. -/
private def presentationDescent (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh X ⥤ (algebraicStackPresentation X).groupoid.QCoh :=
  QCoh.toLQCohFbc X ⋙ LQCohFbc.toGroupoidModules X

/-- A small étale chart of the atlas defines its original point of the prestack. -/
private def reconstructionPoint (X : GroupoidsOver S) [AlgebraicStack X]
    (U : AlgebraicSpace.smallEtaleSite (algebraicStackPresentation X).groupoid.U.left) :=
  (SmallQuotient.atlasToPreQuotientFunctor (algebraicStackPresentation X).groupoid).obj
    (toGroupoidsObj U)

set_option maxHeartbeats 1600000 in
/-- Evaluation of compatible-section reconstruction on an atlas chart recovers
the original prestack section by the two specified extension counits. -/
private def reconstructionSection (X : GroupoidsOver S) [AlgebraicStack X]
    (A : (algebraicStackPresentation X).groupoid.QCoh)
    (U : AlgebraicSpace.smallEtaleSite (algebraicStackPresentation X).groupoid.U.left)
    (s : (LQCohFbc.atlasRestrict X
      ((QCoh.toLQCohFbc X).obj ((presentationReconstruction X).obj A))).obj.val.obj (op U)) :
    ((QuotientQCoh.fromPreQuotient (algebraicStackPresentation X).groupoid).obj A).obj.val.obj
      (op (reconstructionPoint X U)) :=
  let P := algebraicStackPresentation X
  let y := toGroupoidsObj U
  let z := reconstructionPoint X U
  let t := ((LQCohFbc.restrictSpaceEvaluation (atlasMorphism X)).hom.app
    ((QCoh.toLQCohFbc X).obj ((presentationReconstruction X).obj A))).val.app (op U) s
  let t' := ((Presentation.qcohEquivalence P).counitIso.hom.app
    ((QuotientQCoh.fromGroupoidStack P.groupoid).obj A)).hom.val.app
      (op ((toFunctor (SmallQuotient.atlas P.groupoid)).obj y)) t
  ((QuotientQCoh.fromGroupoidStack_comp_pullback P.groupoid).hom.app A).hom.val.app (op z) t'

/-- The top-open chart of the scheme underlying an atlas chart. -/
private def reconstructionTopChart (T : Over S) : AlgebraicSpace.smallEtaleSite (AlgebraicSpace.ofOver T) :=
  (AlgebraicSpace.SmallEtale.toPresentation (AlgebraicSpace.ofOver T)).obj
    ((AlgebraicSpace.SmallEtale.openChart (AlgebraicSpace.Modules.tautologicalChart T)).obj ⊤)

/-- The top-open chart is identified with the original scheme over the base. -/
private def reconstructionTopOverIso (T : Over S) : (reconstructionTopChart T).left ≅ T :=
  Over.isoMk (Scheme.topIso T.left) rfl

/-- The top-open identification commutes with the atlas chart morphism. -/
private def reconstructionChartConditions (X : GroupoidsOver S) [AlgebraicStack X] : Prop :=
  ∀ U : AlgebraicSpace.smallEtaleSite (algebraicStackPresentation X).groupoid.U.left,
    (AlgebraicSpace.ofOverFunctor S).map (reconstructionTopOverIso U.left).hom ≫ U.hom =
      ((@AlgebraicSpace.Modules.restrictPostcompose _ _ _ U.hom U.prop).obj
        (reconstructionTopChart U.left)).hom

/-- The top-open chart and the original atlas chart are isomorphic by the
actual top-open scheme isomorphism. -/
private def reconstructionChartIso (X : GroupoidsOver S) [AlgebraicStack X]
    (hc : reconstructionChartConditions X)
    (U : AlgebraicSpace.smallEtaleSite (algebraicStackPresentation X).groupoid.U.left) :
    (@AlgebraicSpace.Modules.restrictPostcompose _ _ _ U.hom U.prop).obj
        (reconstructionTopChart U.left) ≅ U :=
  MorphismProperty.CostructuredArrow.isoMk (reconstructionTopOverIso U.left)
    trivial trivial (hc U)

set_option maxHeartbeats 1600000 in
/-- Evaluation on an atlas chart is the original Γ-section, followed by
étale pullback-restriction comparison and the top-open restriction inverse. -/
private def reconstructionEvaluationFunction (X : GroupoidsOver S) [AlgebraicStack X]
    (hc : reconstructionChartConditions X)
    (A : (algebraicStackPresentation X).groupoid.QCoh)
    (U : AlgebraicSpace.smallEtaleSite (algebraicStackPresentation X).groupoid.U.left)
    (s : (LQCohFbc.atlasRestrict X
      ((QCoh.toLQCohFbc X).obj ((presentationReconstruction X).obj A))).obj.val.obj (op U)) :
    A.obj.obj.val.obj (op U) :=
  let ep := (pullbackEqIso (yonedaEquiv.symm_apply_apply U.hom)).hom.app A.obj
  let toRestriction := ep.hom ≫
    (@AlgebraicSpace.Modules.restrictFunctorIsoPullback _ _ _ U.hom U.prop).inv.app A.obj.obj
  let t := ((AlgebraicSpace.Modules.restrictToScheme U.left).map toRestriction).val.app
    (op ⊤) (reconstructionSection X A U s)
  (A.obj.obj.val.presheaf.mapIso (reconstructionChartIso X hc U).op).inv t

/-- Atlas evaluation preserves addition and the original chart scalars. -/
private def reconstructionLinearity (X : GroupoidsOver S) [AlgebraicStack X]
    (hc : reconstructionChartConditions X) : Prop :=
  ∀ (A : (algebraicStackPresentation X).groupoid.QCoh)
    (U : AlgebraicSpace.smallEtaleSite (algebraicStackPresentation X).groupoid.U.left),
    (∀ s t, reconstructionEvaluationFunction X hc A U (s + t) =
      reconstructionEvaluationFunction X hc A U s + reconstructionEvaluationFunction X hc A U t) ∧
    (∀ (r : (AlgebraicSpace.structureSheaf (algebraicStackPresentation X).groupoid.U.left).obj.obj
        (op U)) s,
      reconstructionEvaluationFunction X hc A U (r • s) =
        r • reconstructionEvaluationFunction X hc A U s)

set_option maxHeartbeats 1600000 in
/-- The atlas-evaluation section function as a linear map. -/
private def reconstructionEvaluationComponent (X : GroupoidsOver S) [AlgebraicStack X]
    (hc : reconstructionChartConditions X) (hl : reconstructionLinearity X hc)
    (A : (algebraicStackPresentation X).groupoid.QCoh)
    (U : (AlgebraicSpace.smallEtaleSite (algebraicStackPresentation X).groupoid.U.left)ᵒᵖ) :
    (((presentationReconstruction X ⋙ presentationDescent X).obj A).obj.obj.val.obj U) ⟶
      A.obj.obj.val.obj U :=
  ConcreteCategory.ofHom
    (C := ModuleCat ((AlgebraicSpace.structureSheaf (algebraicStackPresentation X).groupoid.U.left).obj.obj U))
    (X := ((presentationReconstruction X ⋙ presentationDescent X).obj A).obj.obj.val.obj U)
    (Y := A.obj.obj.val.obj U)
    { toFun := reconstructionEvaluationFunction X hc A U.unop
      map_add' := (hl A U.unop).1
      map_smul' := (hl A U.unop).2 }

/-- Atlas evaluation commutes with restriction along small étale chart maps. -/
private def reconstructionNaturality (X : GroupoidsOver S) [AlgebraicStack X]
    (hc : reconstructionChartConditions X) (hl : reconstructionLinearity X hc) : Prop :=
  ∀ (A : (algebraicStackPresentation X).groupoid.QCoh)
    {U V : (AlgebraicSpace.smallEtaleSite (algebraicStackPresentation X).groupoid.U.left)ᵒᵖ}
    (a : U ⟶ V),
    (((presentationReconstruction X ⋙ presentationDescent X).obj A).obj.obj.val.map a) ≫
        (ModuleCat.restrictScalars
          ((AlgebraicSpace.structureSheaf (algebraicStackPresentation X).groupoid.U.left).obj.map a).hom).map
            (reconstructionEvaluationComponent X hc hl A V) =
      reconstructionEvaluationComponent X hc hl A U ≫ A.obj.obj.val.map a

/-- Atlas evaluation defines a morphism of the underlying quasi-coherent modules. -/
private def reconstructionModuleMap (X : GroupoidsOver S) [AlgebraicStack X]
    (hc : reconstructionChartConditions X) (hl : reconstructionLinearity X hc)
    (hn : reconstructionNaturality X hc hl)
    (A : (algebraicStackPresentation X).groupoid.QCoh) :
    ((presentationReconstruction X ⋙ presentationDescent X).obj A).obj ⟶ A.obj :=
  ObjectProperty.homMk
    { val := { app := reconstructionEvaluationComponent X hc hl A
               naturality := fun {_ _} a ↦ hn A a } }

/-- Atlas evaluation intertwines the reconstructed and original descent actions. -/
private def reconstructionEquivariance (X : GroupoidsOver S) [AlgebraicStack X]
    (hc : reconstructionChartConditions X) (hl : reconstructionLinearity X hc)
    (hn : reconstructionNaturality X hc hl) : Prop :=
  ∀ A : (algebraicStackPresentation X).groupoid.QCoh,
    (AlgebraicSpace.QCoh.pullback (algebraicStackPresentation X).groupoid.t.left).map
        (reconstructionModuleMap X hc hl hn A) ≫ A.action =
      ((presentationReconstruction X ⋙ presentationDescent X).obj A).action ≫
        (AlgebraicSpace.QCoh.pullback (algebraicStackPresentation X).groupoid.s.left).map
          (reconstructionModuleMap X hc hl hn A)

/-- Evaluation of reconstructed Γ-sections gives the specified equivariant comparison. -/
private def reconstructionCounitComponent (X : GroupoidsOver S) [AlgebraicStack X]
    (hc : reconstructionChartConditions X) (hl : reconstructionLinearity X hc)
    (hn : reconstructionNaturality X hc hl) (he : reconstructionEquivariance X hc hl hn)
    (A : (algebraicStackPresentation X).groupoid.QCoh) :
    (presentationReconstruction X ⋙ presentationDescent X).obj A ⟶ A :=
  System.Hom.of (reconstructionModuleMap X hc hl hn A) (he A)

/-- Restriction to a smooth presentation is fully faithful, and the specified
Γ-evaluation comparison is an invertible natural equivariant morphism. -/
private theorem QCoh.presentationDescentEquivalence_laws (X : GroupoidsOver S) [AlgebraicStack X] :
    (∀ G H : QCoh X, Function.Bijective
      ((presentationDescent X).map : (G ⟶ H) → _)) ∧
    reconstructionChartConditions X ∧
    ∀ hc : reconstructionChartConditions X,
      reconstructionLinearity X hc ∧ ∀ hl : reconstructionLinearity X hc,
        reconstructionNaturality X hc hl ∧ ∀ hn : reconstructionNaturality X hc hl,
          reconstructionEquivariance X hc hl hn ∧ ∀ he : reconstructionEquivariance X hc hl hn,
            (∀ A, IsIso (reconstructionCounitComponent X hc hl hn he A)) ∧
            (∀ {A B : (algebraicStackPresentation X).groupoid.QCoh} (a : A ⟶ B),
              (presentationReconstruction X ⋙ presentationDescent X).map a ≫
                  reconstructionCounitComponent X hc hl hn he B =
                reconstructionCounitComponent X hc hl hn he A ≫ a) := sorry

/-- The inverse on morphisms of presentation descent is the unique inverse
of its specified restriction map. -/
private def presentationDescentFullyFaithful (X : GroupoidsOver S) [AlgebraicStack X] :
    (presentationDescent X).FullyFaithful where
  preimage {G H} :=
    (Equiv.ofBijective _ ((QCoh.presentationDescentEquivalence_laws X).1 G H)).symm
  map_preimage {G H} a :=
    (Equiv.ofBijective _ ((QCoh.presentationDescentEquivalence_laws X).1 G H)).apply_symm_apply a
  preimage_map {G H} a :=
    (Equiv.ofBijective _ ((QCoh.presentationDescentEquivalence_laws X).1 G H)).symm_apply_apply a

/-- The reconstruction counit is the actual evaluation of Γ-sections on the atlas. -/
private def presentationCounitIso (X : GroupoidsOver S) [AlgebraicStack X] :
    presentationReconstruction X ⋙ presentationDescent X ≅
      𝟭 (algebraicStackPresentation X).groupoid.QCoh :=
  let hc := (QCoh.presentationDescentEquivalence_laws X).2.1
  let hl := ((QCoh.presentationDescentEquivalence_laws X).2.2 hc).1
  let hn := (((QCoh.presentationDescentEquivalence_laws X).2.2 hc).2 hl).1
  let he := ((((QCoh.presentationDescentEquivalence_laws X).2.2 hc).2 hl).2 hn).1
  let h := ((((QCoh.presentationDescentEquivalence_laws X).2.2 hc).2 hl).2 hn).2 he
  NatIso.ofComponents (fun A ↦ @asIso _ _ _ _
    (reconstructionCounitComponent X hc hl hn he A) (h.1 A)) (fun a ↦ h.2 a)

/-- The presentation unit is the unique lift of the inverse Γ-evaluation
counit under the fully faithful restriction functor. -/
private def presentationUnitIso (X : GroupoidsOver S) [AlgebraicStack X] :
    𝟭 (QCoh X) ≅ presentationDescent X ⋙ presentationReconstruction X :=
  ((presentationDescentFullyFaithful X).whiskeringRight (QCoh X)).preimageIso
    (Functor.leftUnitor (presentationDescent X) ≪≫
      (Functor.rightUnitor (presentationDescent X)).symm ≪≫
      Functor.isoWhiskerLeft (presentationDescent X) (presentationCounitIso X).symm ≪≫
      (Functor.associator (presentationDescent X) (presentationReconstruction X)
        (presentationDescent X)).symm)

/-- Quasi-coherent modules are equivalent to their smooth-presentation
descent data, with concrete Γ-reconstruction as inverse. -/
def QCoh.presentationDescentEquivalence (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh X ≌ (algebraicStackPresentation X).groupoid.QCoh :=
  CategoryTheory.Equivalence.mk (presentationDescent X) (presentationReconstruction X)
    (presentationUnitIso X) (presentationCounitIso X)

/-- Morphisms from a quasi-coherent module to a flat-base-change module
are recovered uniquely by restriction to the smooth presentation. -/
theorem QCoh.toLQCohFbc_homRestriction_bijective (X : GroupoidsOver S) [AlgebraicStack X]
    (G : QCoh X) (F : LQCohFbc X) :
    Function.Bijective ((LQCohFbc.toGroupoidModules X).map :
      ((QCoh.toLQCohFbc X).obj G ⟶ F) →
        ((LQCohFbc.toGroupoidModules X).obj ((QCoh.toLQCohFbc X).obj G) ⟶
          (LQCohFbc.toGroupoidModules X).obj F)) := sorry

/-- The adjunction Hom equivalence is descent of morphisms followed by
the explicit presentation equivalence. -/
def QCoh.toLQCohFbcHomEquiv (X : GroupoidsOver S) [AlgebraicStack X]
    (G : QCoh X) (F : LQCohFbc X) :
    ((QCoh.toLQCohFbc X).obj G ⟶ F) ≃ (G ⟶ (LQCohFbc.toQCoh X).obj F) :=
  (Equiv.ofBijective _ (QCoh.toLQCohFbc_homRestriction_bijective X G F)).trans
    ((QCoh.presentationDescentEquivalence X).toAdjunction.homEquiv G
      ((LQCohFbc.toGroupoidModules X).obj F))

/-- Descent and reconstruction give a Hom equivalence natural in both modules. -/
theorem QCoh.toLQCohFbc_homEquiv_naturality (X : GroupoidsOver S) [AlgebraicStack X] :
    (∀ {G' G : QCoh X} {F : LQCohFbc X} (a : G' ⟶ G)
      (b : G ⟶ (LQCohFbc.toQCoh X).obj F),
      (QCoh.toLQCohFbcHomEquiv X G' F).symm (a ≫ b) =
        (QCoh.toLQCohFbc X).map a ≫ (QCoh.toLQCohFbcHomEquiv X G F).symm b) ∧
    (∀ {G : QCoh X} {F F' : LQCohFbc X} (a : (QCoh.toLQCohFbc X).obj G ⟶ F)
      (b : F ⟶ F'),
      QCoh.toLQCohFbcHomEquiv X G F' (a ≫ b) =
        QCoh.toLQCohFbcHomEquiv X G F a ≫ (LQCohFbc.toQCoh X).map b) := sorry

/-- The topology-restriction inclusion is adjoint to the explicit
quasi-coherent reconstruction functor. -/
def QCoh.toLQCohFbcAdjunction (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := QCoh.toLQCohFbcHomEquiv X
      homEquiv_naturality_left_symm := (QCoh.toLQCohFbc_homEquiv_naturality X).1
      homEquiv_naturality_right := (QCoh.toLQCohFbc_homEquiv_naturality X).2 }

/-- The constructed quasi-coherent functor is right adjoint to the actual inclusion. -/
theorem QCoh.toLQCohFbc_isRightAdjoint_toQCoh (X : GroupoidsOver S) [AlgebraicStack X] :
    Nonempty (QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) := sorry

/-- The inclusion of quasi-coherent modules has the constructed right adjoint. -/
instance QCoh.toLQCohFbc_isLeftAdjoint (X : GroupoidsOver S) [AlgebraicStack X] :
    (QCoh.toLQCohFbc X).IsLeftAdjoint where
  exists_rightAdjoint := ⟨LQCohFbc.toQCoh X, ⟨QCoh.toLQCohFbcAdjunction X⟩⟩

/-- Inclusion followed by quasi-coherent reconstruction is naturally isomorphic
to the identity, through the actual adjunction unit. -/
def QCoh.toLQCohFbc_comp_toQCoh (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh.toLQCohFbc X ⋙ LQCohFbc.toQCoh X ≅ 𝟭 (QCoh X) :=
  (asIso (QCoh.toLQCohFbcAdjunction X).unit).symm

end AlgebraicGeometry.GroupoidsOver
