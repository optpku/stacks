/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.PullbackCoherence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Reconstruction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small.Comparison

/-! # Equivariant quasi-coherent modules and quotient stacks -/

@[expose] public section
set_option backward.privateInPublic true
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.GroupoidsOver AlgebraicGeometry.GroupoidAlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace.QuotientQCoh
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.ObjectProperty CategoryTheory.Sheaf.InternalModule CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory
noncomputable section
universe u
namespace AlgebraicGeometry.GroupoidsOver.QCoh
variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- Restriction of the atlas pullback to the small étale site of `U`. -/
def atlasRestrict (F : QCoh (SmallQuotient.quotientStack G)) : AlgebraicSpace.QCoh G.U.left :=
  (restrict ((Bicategory.Equivalence.id G.U.left.toGroupoids))).obj ((pullback (SmallQuotient.atlas G)).obj F)

/-- `atlasRestrict F` is restriction of `π^* F` along the identity presentation of `U`. -/
theorem atlasRestrict_eq (F : QCoh (SmallQuotient.quotientStack G)) :
    atlasRestrict G F =
      (restrict ((Bicategory.Equivalence.id G.U.left.toGroupoids))).obj ((pullback (SmallQuotient.atlas G)).obj F) :=
  rfl

/-- Restriction after pullback along `toGroupoids.map G.s.left` compares with
small-étale pullback along `G.s.left`. -/
private def restrict_atlasPullbackIso_source :
    pullback (AlgebraicSpace.toGroupoids.map G.s.left) ⋙ restrict ((Bicategory.Equivalence.id G.R.left.toGroupoids)) ≅
      restrict ((Bicategory.Equivalence.id G.U.left.toGroupoids)) ⋙ AlgebraicSpace.QCoh.pullback G.s.left :=
  restrictPullbackIso (Bicategory.Equivalence.id G.R.left.toGroupoids)
      (Bicategory.Equivalence.id G.U.left.toGroupoids)
      (AlgebraicSpace.toGroupoids.map G.s.left) ≪≫
    Functor.isoWhiskerLeft (restrict (Bicategory.Equivalence.id G.U.left.toGroupoids))
      (GroupoidAlgebraicSpace.pullbackEqIso
        (moduleComparisonSpaceMorphism_toGroupoids G.s.left))

/-- Restriction after pullback along `toGroupoids.map G.t.left` compares with
small-étale pullback along `G.t.left`. -/
private def restrict_atlasPullbackIso_target :
    pullback (AlgebraicSpace.toGroupoids.map G.t.left) ⋙ restrict ((Bicategory.Equivalence.id G.R.left.toGroupoids)) ≅
      restrict ((Bicategory.Equivalence.id G.U.left.toGroupoids)) ⋙ AlgebraicSpace.QCoh.pullback G.t.left :=
  restrictPullbackIso (Bicategory.Equivalence.id G.R.left.toGroupoids)
      (Bicategory.Equivalence.id G.U.left.toGroupoids)
      (AlgebraicSpace.toGroupoids.map G.t.left) ≪≫
    Functor.isoWhiskerLeft (restrict (Bicategory.Equivalence.id G.U.left.toGroupoids))
      (GroupoidAlgebraicSpace.pullbackEqIso
        (moduleComparisonSpaceMorphism_toGroupoids G.t.left))

/-- The canonical atlas two-isomorphism induces the action on atlas pullback. -/
private def atlasActionAux (F : QCoh (SmallQuotient.quotientStack G)) :
    (pullback (AlgebraicSpace.toGroupoids.map G.t.left)).obj ((pullback (SmallQuotient.atlas G)).obj F) ⟶
      (pullback (AlgebraicSpace.toGroupoids.map G.s.left)).obj ((pullback (SmallQuotient.atlas G)).obj F) :=
  (pullback_comp (AlgebraicSpace.toGroupoids.map G.t.left) (SmallQuotient.atlas G)).inv.app F ≫
    (pullbackMap (SmallQuotient.sourceTargetIso G).hom).app F ≫
      (pullback_comp (AlgebraicSpace.toGroupoids.map G.s.left) (SmallQuotient.atlas G)).hom.app F

/-- The equivariance map `α : t_small^* G ⟶ s_small^* G` of `atlasRestrict F`. -/
def action (F : QCoh (SmallQuotient.quotientStack G)) :
    (AlgebraicSpace.QCoh.pullback G.t.left).obj (atlasRestrict G F) ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj (atlasRestrict G F) :=
  (restrict_atlasPullbackIso_target G).inv.app ((pullback (SmallQuotient.atlas G)).obj F) ≫
    (restrict ((Bicategory.Equivalence.id G.R.left.toGroupoids))).map (atlasActionAux G F) ≫
      (restrict_atlasPullbackIso_source G).hom.app ((pullback (SmallQuotient.atlas G)).obj F)

/-- `action F` is the transport of `atlasActionAux` through the source and target
restriction comparisons. -/
theorem action_spec (F : QCoh (SmallQuotient.quotientStack G)) :
    action G F =
      (restrict_atlasPullbackIso_target G).inv.app ((pullback (SmallQuotient.atlas G)).obj F) ≫
        (restrict ((Bicategory.Equivalence.id G.R.left.toGroupoids))).map (atlasActionAux G F) ≫
          (restrict_atlasPullbackIso_source G).hom.app ((pullback (SmallQuotient.atlas G)).obj F) :=
  rfl

/-- The atlas equivariance map satisfies the cocycle condition on
`R ×_{s,U,t} R`. -/
private theorem action_cocycle (F : QCoh (SmallQuotient.quotientStack G)) :
    GroupoidAlgebraicSpace.Cocycle G (atlasRestrict G F) (action G F) :=
  sorry

/-- The atlas equivariance map satisfies the unit condition along the identity
section of the groupoid. -/
private theorem action_unit (F : QCoh (SmallQuotient.quotientStack G)) :
    GroupoidAlgebraicSpace.Unit G (atlasRestrict G F) (action G F) :=
  sorry

/-- Atlas restriction of morphisms commutes with the canonical descent actions. -/
private theorem toGroupoid_laws {F F' : QCoh (SmallQuotient.quotientStack G)} (f : F ⟶ F') :
    let m := (restrict (Bicategory.Equivalence.id G.U.left.toGroupoids)).map
      ((pullback (SmallQuotient.atlas G)).map f)
    (AlgebraicSpace.QCoh.pullback G.t.left).map m ≫ action G F' =
      action G F ≫ (AlgebraicSpace.QCoh.pullback G.s.left).map m := sorry

/-- Atlas restriction with its canonical descent action defines an equivariant module. -/
def toGroupoid : QCoh (SmallQuotient.quotientStack G) ⥤ G.QCoh where
  obj F := GroupoidAlgebraicSpace.QCoh.of (atlasRestrict G F) (action G F)
    (action_cocycle G F) (action_unit G F)
  map f := System.Hom.of
    ((restrict (Bicategory.Equivalence.id G.U.left.toGroupoids)).map
      ((pullback (SmallQuotient.atlas G)).map f)) (toGroupoid_laws G f)
  map_id F := System.Hom.ext
    ((congrArg (fun a => (restrict (Bicategory.Equivalence.id G.U.left.toGroupoids)).map a)
      ((pullback (SmallQuotient.atlas G)).map_id F)).trans
        ((restrict (Bicategory.Equivalence.id G.U.left.toGroupoids)).map_id _))
  map_comp f g := System.Hom.ext
    ((congrArg (fun a => (restrict (Bicategory.Equivalence.id G.U.left.toGroupoids)).map a)
      ((pullback (SmallQuotient.atlas G)).map_comp f g)).trans
        ((restrict (Bicategory.Equivalence.id G.U.left.toGroupoids)).map_comp _ _))

/-- The underlying quasi-coherent module of `toGroupoid F` is `x^* F` restricted
to the small étale site of `U`. -/
theorem toGroupoid_obj (F : QCoh (SmallQuotient.quotientStack G)) :
    GroupoidAlgebraicSpace.QCoh.obj ((toGroupoid G).obj F) = atlasRestrict G F :=
  rfl

/-- The equivariance map of `toGroupoid F` is the atlas 2-cell action `α`. -/
theorem toGroupoid_action (F : QCoh (SmallQuotient.quotientStack G)) :
    GroupoidAlgebraicSpace.QCoh.action ((toGroupoid G).obj F) = action G F :=
  rfl

/-- The category fibred in groupoids associated to the object space of `G`. -/
private def objectGroupoids : GroupoidsOver S :=
  (G.U.left).toGroupoids

/-- The object of `[U /ₚ R]` obtained by applying the object inclusion to an object of
`𝒮_U`. -/
private def atlasToPreQuotientObj (y : (objectGroupoids G).total) : (SmallQuotient.preQuotient G).total :=
  (toCartesianBasedFunctor (SmallQuotient.atlasToPreQuotient G)).toFunctor.obj y

/-- The object of `𝒮_U` with the same scheme and `U`-point as an object of `[U /ₚ R]`. -/
private def objectPoint (x : (SmallQuotient.preQuotient G).total) : (objectGroupoids G).total :=
  Opposite.op ⟨Opposite.op x.base, x.fiber⟩

/-- Object-inclusion of `objectPoint x` recovers `x`. -/
private theorem atlasToPreQuotient_objectPoint (x : (SmallQuotient.preQuotient G).total) :
    atlasToPreQuotientObj G (objectPoint G x) = x :=
  sorry

/-- Underlying sheaf of quasi-coherent pullback along the object inclusion. -/
private def pullback_fromPreQuotient_compιIso (A : G.QCoh) :
    ((pullback (SmallQuotient.atlasToPreQuotient G)).obj ((fromPreQuotient G).obj A)).obj ≅
      (modulePullback (SmallQuotient.atlasToPreQuotient G)).obj ((fromPreQuotient G).obj A).obj :=
  (FullSubcategory.restrict.compιIso (modulePullback (SmallQuotient.atlasToPreQuotient G))
      (modulePullback_le_inverseImage (SmallQuotient.atlasToPreQuotient G))).app
    ((fromPreQuotient G).obj A)

/-- Object-equality transport of a prequotient module sheaf along
`atlasToPreQuotient_objectPoint`. -/
private def fromPreQuotient_objectPoint_eqToHom (A : G.QCoh) (x : (SmallQuotient.preQuotient G).total) :
    ((fromPreQuotient G).obj A).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x))) ⟶
      ((fromPreQuotient G).obj A).obj.val.obj (op x) :=
  ((fromPreQuotient G).obj A).obj.val.map
    (eqToHom (congrArg Opposite.op (atlasToPreQuotient_objectPoint G x)))

/-- Inverse object-equality transport of a prequotient module sheaf along
`atlasToPreQuotient_objectPoint`. -/
private def fromPreQuotient_objectPoint_eqToHom_inv (A : G.QCoh)
    (x : (SmallQuotient.preQuotient G).total) :
    ((fromPreQuotient G).obj A).obj.val.obj (op x) ⟶
      ((fromPreQuotient G).obj A).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x))) :=
  ((fromPreQuotient G).obj A).obj.val.map
    (eqToHom (congrArg Opposite.op (atlasToPreQuotient_objectPoint G x).symm))

/-- Object-equality transport of stackification pullback along
`atlasToPreQuotient_objectPoint`. -/
private def stackification_objectPoint_eqToHom (F : QCoh (SmallQuotient.quotientStack G))
    (x : (SmallQuotient.preQuotient G).total) :
    ((pullback (SmallQuotient.stackificationHom G)).obj F).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x))) ⟶
      ((pullback (SmallQuotient.stackificationHom G)).obj F).obj.val.obj (op x) :=
  ((pullback (SmallQuotient.stackificationHom G)).obj F).obj.val.map
    (eqToHom (congrArg Opposite.op (atlasToPreQuotient_objectPoint G x)))

/-- Inverse object-equality transport of stackification pullback along
`atlasToPreQuotient_objectPoint`. -/
private def stackification_objectPoint_eqToHom_inv (F : QCoh (SmallQuotient.quotientStack G))
    (x : (SmallQuotient.preQuotient G).total) :
    ((pullback (SmallQuotient.stackificationHom G)).obj F).obj.val.obj (op x) ⟶
      ((pullback (SmallQuotient.stackificationHom G)).obj F).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x))) :=
  ((pullback (SmallQuotient.stackificationHom G)).obj F).obj.val.map
    (eqToHom (congrArg Opposite.op (atlasToPreQuotient_objectPoint G x).symm))

/-- Inclusion comparison of object-inclusion pullback of the Γ-sheaf, evaluated
at an object of `𝒮_U`. -/
private def pullback_fromPreQuotient_evalIso (A : G.QCoh)
    (y : (objectGroupoids G).totalᵒᵖ) :
    ((pullback (SmallQuotient.atlasToPreQuotient G)).obj ((fromPreQuotient G).obj A)).obj.val.obj y ≅
      ((modulePullback (SmallQuotient.atlasToPreQuotient G)).obj
        ((fromPreQuotient G).obj A).obj).val.obj y :=
  { hom := (pullback_fromPreQuotient_compιIso G A).hom.val.app y
    inv := (pullback_fromPreQuotient_compιIso G A).inv.val.app y
    hom_inv_id := by
      have h := congrArg (fun f => f.val.app y) (pullback_fromPreQuotient_compιIso G A).hom_inv_id
      exact h
    inv_hom_id := by
      have h := congrArg (fun f => f.val.app y) (pullback_fromPreQuotient_compιIso G A).inv_hom_id
      exact h }

/-- Global sections on an atlas point, first restricted along
`structureSheafToPushforward` and then along `structureSheafMap` of the object
inclusion. The two coefficient actions are retained on the original carrier. -/
def atlasGammaSectionObj (A : G.QCoh) (y : G.U.left.toGroupoids.totalᵒᵖ) :
    ModuleCat.{u} ((structureSheaf G.U.left.toGroupoids).obj.obj y) :=
  (ModuleCat.restrictScalars
      ((structureSheafMap (SmallQuotient.atlasToPreQuotient G)).hom.app y).hom).obj
    (fromPreQuotient_objModule G A (atlasToPreQuotientObj G y.unop))

/-- Evaluation of the inverse-image module at the same atlas point. -/
def atlasPiStarSectionObj (A : G.QCoh) (y : G.U.left.toGroupoids.totalᵒᵖ) :
    ModuleCat.{u} ((structureSheaf G.U.left.toGroupoids).obj.obj y) :=
  ((piStar (Bicategory.Equivalence.id G.U.left.toGroupoids)).obj A.obj).obj.val.obj y

/-- The section object is exactly the scalar restriction of reconstructed
prequotient evaluation, rather than a choice of an isomorphic module. -/
theorem atlasGammaSectionObj_eq (A : G.QCoh) (y : G.U.left.toGroupoids.totalᵒᵖ) :
    atlasGammaSectionObj G A y =
      (ModuleCat.restrictScalars
        ((structureSheafMap (SmallQuotient.atlasToPreQuotient G)).hom.app y).hom).obj
        (((fromPreQuotient G).obj A).obj.val.obj
          (op ((toCartesianBasedFunctor (SmallQuotient.atlasToPreQuotient G)).toFunctor.obj y.unop))) :=
  rfl

set_option maxHeartbeats 800000 in
/-- Scalar multiplication applies the two specified ring homomorphisms in order. -/
theorem atlasGammaSectionObj_smul (A : G.QCoh) (y : G.U.left.toGroupoids.totalᵒᵖ)
    (r : (structureSheaf G.U.left.toGroupoids).obj.obj y) (t : atlasGammaSectionObj G A y) :
    let x := (toCartesianBasedFunctor (SmallQuotient.atlasToPreQuotient G)).toFunctor.obj y.unop
    let M := atlasGammaSectionObj G A y
    let N := gammaObj G A x
    @SMul.smul _ M M.isModule.toDistribMulAction.toMulAction.toSMul r t =
      @SMul.smul _ N N.isModule.toDistribMulAction.toMulAction.toSMul
        (((structureSheafToPushforward (SmallQuotient.preQuotient G)).hom.app
          (op x)).hom
          (((structureSheafMap (SmallQuotient.atlasToPreQuotient G)).hom.app y).hom r)) t :=
  rfl

/-- Equivariant-module morphisms act on the same atlas section objects by the
original global-sections map with both scalar restrictions. -/
def atlasGammaSectionMap {A A' : G.QCoh} (f : A ⟶ A')
    (y : G.U.left.toGroupoids.totalᵒᵖ) :
    atlasGammaSectionObj G A y ⟶ atlasGammaSectionObj G A' y :=
  (ModuleCat.restrictScalars
      ((structureSheafMap (SmallQuotient.atlasToPreQuotient G)).hom.app y).hom).map
    ((ModuleCat.restrictScalars
      ((structureSheafToPushforward (SmallQuotient.preQuotient G)).hom.app
        (op (atlasToPreQuotientObj G y.unop))).hom).map
      (gammaObjMap G f (atlasToPreQuotientObj G y.unop)))

/-- The induced map retains the original global-sections function. -/
theorem atlasGammaSectionMap_apply {A A' : G.QCoh} (f : A ⟶ A')
    (y : G.U.left.toGroupoids.totalᵒᵖ) (t : atlasGammaSectionObj G A y) :
    atlasGammaSectionMap G f y t =
      gammaObjMap G f
        ((toCartesianBasedFunctor (SmallQuotient.atlasToPreQuotient G)).toFunctor.obj y.unop) t :=
  rfl

/-- The atlas section map agrees with evaluation of the reconstructed morphism
followed by the object-inclusion scalar restriction. -/
theorem atlasGammaSectionMap_eq {A A' : G.QCoh} (f : A ⟶ A')
    (y : G.U.left.toGroupoids.totalᵒᵖ) :
    atlasGammaSectionMap G f y =
      (ModuleCat.restrictScalars
        ((structureSheafMap (SmallQuotient.atlasToPreQuotient G)).hom.app y).hom).map
        (((fromPreQuotient G).map f).hom.val.app
          (op ((toCartesianBasedFunctor (SmallQuotient.atlasToPreQuotient G)).toFunctor.obj y.unop))) :=
  rfl

/-- Object-inclusion pullback of the Γ-sheaf, evaluated and transported to
`Γ(T, u_small^* A)` over `𝒪_{𝒮_U}`. -/
private def fromPreQuotient_piStar_gammaIso (A : G.QCoh)
    (y : (objectGroupoids G).totalᵒᵖ) :
    ((pullback (SmallQuotient.atlasToPreQuotient G)).obj ((fromPreQuotient G).obj A)).obj.val.obj y ≅
      atlasGammaSectionObj G A y :=
  pullback_fromPreQuotient_evalIso G A y ≪≫
    modulePullback_evalIso (SmallQuotient.atlasToPreQuotient G)
      ((fromPreQuotient G).obj A).obj y.unop ≪≫
    (ModuleCat.restrictScalars
        ((structureSheafMap (SmallQuotient.atlasToPreQuotient G)).hom.app y).hom).mapIso
      (eqToIso (fromPreQuotient_obj G A (atlasToPreQuotientObj G y.unop)))

/-- The top-open chart of a represented scheme. -/
private def topChart (T : Over S) : smallEtaleSite (ofOver T) :=
  (SmallEtale.toPresentation (ofOver T)).obj
    ((SmallEtale.openChart (AlgebraicSpace.Modules.tautologicalChart T)).obj ⊤)

/-- The top-open chart has the same underlying scheme over the base. -/
private def topChartIso (T : Over S) : (topChart T).left ≅ T :=
  Over.isoMk (Scheme.topIso T.left) rfl

/-- A point pulled back to the top-open chart is isomorphic to the original point. -/
private def topPointIso (y : (objectGroupoids G).total) :
    (toCartesianBasedFunctor (AlgebraicSpace.toGroupoids.map
      (pointHom G (atlasToPreQuotientObj G y)))).toFunctor.obj
        ((smallEtaleFunctor (ofOver (atlasToPreQuotientObj G y).base)
          (ofOver (atlasToPreQuotientObj G y).base).toGroupoids
          (Bicategory.Equivalence.id _)).obj (topChart (atlasToPreQuotientObj G y).base)) ≅ y := by
  let T := (atlasToPreQuotientObj G y).base
  refine (CategoryOfElements.isoMk y.unop _ (by
    change op T ≅ op (topChart T).left
    exact (topChartIso T).op) ?_).op
  change G.U.left.functorOfPoints.map (topChartIso T).hom.op y.unop.snd = _
  rfl

/-- Global sections of the pulled-back module map to the inverse image at the
original point through the chart adjunction and fppf sheafification comparison. -/
private def piStar_gamma_forward (A : G.QCoh) (y : (objectGroupoids G).totalᵒᵖ) :
    atlasGammaSectionObj G A y →
      atlasPiStarSectionObj G A y := by
  let x := atlasToPreQuotientObj G y.unop
  let f := pointHom G x
  let eT := Bicategory.Equivalence.id (ofOver x.base).toGroupoids
  let eU := Bicategory.Equivalence.id G.U.left.toGroupoids
  let H := (piStar eU).obj A.obj
  let k := (AlgebraicSpace.QCoh.pullback f).map (restrict_piStarUnit eU A.obj) ≫
    (GroupoidAlgebraicSpace.pullbackEqIso
      (moduleComparisonSpaceMorphism_toGroupoids f).symm).hom.app ((restrict eU).obj H) ≫
    (restrictPullbackIso eT eU (AlgebraicSpace.toGroupoids.map f)).inv.app H
  let g := (AlgebraicSpace.Modules.restrictToScheme x.base).map k.hom
  intro t
  let t' := g.val.app (op ⊤) t
  exact H.obj.val.presheaf.map (topPointIso G y.unop).inv.op t'

/-- The canonical comparison on sections is bijective. -/
private theorem piStar_gamma_eval_bijective (A : G.QCoh)
    (y : (objectGroupoids G).totalᵒᵖ) :
    Function.Bijective (piStar_gamma_forward G A y) := sorry

/-- The canonical comparison on sections preserves addition and scalar multiplication. -/
private theorem piStar_gamma_eval_laws (A : G.QCoh)
    (y : (objectGroupoids G).totalᵒᵖ) :
    let M : ModuleCat.{u} ((structureSheaf (objectGroupoids G)).obj.obj y) :=
      atlasGammaSectionObj G A y
    let N : ModuleCat.{u} ((structureSheaf (objectGroupoids G)).obj.obj y) :=
      atlasPiStarSectionObj G A y
    (∀ a b : M, piStar_gamma_forward G A y (a + b) =
      (piStar_gamma_forward G A y a : N) + (piStar_gamma_forward G A y b : N)) ∧
    (∀ (r : (structureSheaf (objectGroupoids G)).obj.obj y) (a : M),
      piStar_gamma_forward G A y (r • a) = @SMul.smul _ N N.isModule.toDistribMulAction.toMulAction.toSMul r
        (piStar_gamma_forward G A y a)) := sorry

/-- The section comparison as a linear map over the original coefficient ring. -/
private def piStar_gamma_linear (A : G.QCoh) (y : (objectGroupoids G).totalᵒᵖ) :
    atlasGammaSectionObj G A y ⟶
      atlasPiStarSectionObj G A y := by
  let M : ModuleCat.{u} ((structureSheaf (objectGroupoids G)).obj.obj y) :=
    atlasGammaSectionObj G A y
  let N : ModuleCat.{u} ((structureSheaf (objectGroupoids G)).obj.obj y) :=
    atlasPiStarSectionObj G A y
  exact @ModuleCat.ofHom _ _ M N M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule
    { toFun := piStar_gamma_forward G A y
      map_add' := (piStar_gamma_eval_laws G A y).1
      map_smul' := (piStar_gamma_eval_laws G A y).2 }

/-- A preimage section of a fixed linear map, with zero on an empty fibre. -/
private def inverseSection {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (y : N) : M := by
  classical
  exact if h : ∃ x, f x = y then h.choose else 0

private theorem inverseSection_left {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (hf : Function.Bijective f) :
    Function.LeftInverse (inverseSection f) f := by
  intro x
  dsimp [inverseSection]
  rw [dif_pos ⟨x, rfl⟩]
  exact hf.1 (Exists.choose_spec (⟨x, rfl⟩ : ∃ y, f y = f x))

private theorem inverseSection_right {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (hf : Function.Bijective f) :
    Function.RightInverse (inverseSection f) f := by
  intro y
  dsimp [inverseSection]
  rw [dif_pos (hf.2 y)]
  exact Exists.choose_spec (hf.2 y)

set_option maxHeartbeats 800000 in
/-- The canonical comparison of scalar-transported global sections with
inverse-image evaluation, with inverse in the fibres of its forward map. -/
private def piStar_gamma_evalIso (A : G.QCoh) (y : (objectGroupoids G).totalᵒᵖ) :
    atlasGammaSectionObj G A y ≅
      atlasPiStarSectionObj G A y := by
  let f := piStar_gamma_linear G A y
  let M : ModuleCat.{u} ((structureSheaf (objectGroupoids G)).obj.obj y) :=
    atlasGammaSectionObj G A y
  let N : ModuleCat.{u} ((structureSheaf (objectGroupoids G)).obj.obj y) :=
    atlasPiStarSectionObj G A y
  refine { hom := f, inv := ?_, hom_inv_id := ?_, inv_hom_id := ?_ }
  · exact @ModuleCat.ofHom _ _ N M N.isAddCommGroup N.isModule M.isAddCommGroup M.isModule
      ((piStar_gamma_linear G A y).hom.inverse
    (inverseSection (piStar_gamma_linear G A y))
    (inverseSection_left (piStar_gamma_linear G A y) (piStar_gamma_eval_bijective G A y))
    (inverseSection_right (piStar_gamma_linear G A y) (piStar_gamma_eval_bijective G A y)))
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact inverseSection_left (piStar_gamma_linear G A y) (piStar_gamma_eval_bijective G A y) t
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact inverseSection_right (piStar_gamma_linear G A y) (piStar_gamma_eval_bijective G A y) t

/-- Evaluation of object-inclusion pullback of the Γ-sheaf identifies with
evaluation of `π_U^* A`. -/
private def fromPreQuotient_piStar_evalIso (A : G.QCoh)
    (y : (objectGroupoids G).totalᵒᵖ) :
    ((pullback (SmallQuotient.atlasToPreQuotient G)).obj ((fromPreQuotient G).obj A)).obj.val.obj y ≅
      atlasPiStarSectionObj G A y :=
  fromPreQuotient_piStar_gammaIso G A y ≪≫
    piStar_gamma_evalIso G A y

/-- The section comparisons commute with restriction along morphisms of points. -/
private theorem fromPreQuotient_piStar_objIso_laws (A : G.QCoh) :
    ∀ {x y : (objectGroupoids G).totalᵒᵖ} (a : x ⟶ y),
      (((pullback (SmallQuotient.atlasToPreQuotient G)).obj ((fromPreQuotient G).obj A)).obj.val.map a) ≫
        (ModuleCat.restrictScalars ((structureSheaf (objectGroupoids G)).obj.map a).hom).map
          (fromPreQuotient_piStar_evalIso G A y).hom =
      (fromPreQuotient_piStar_evalIso G A x).hom ≫
        (((piStar (Bicategory.Equivalence.id G.U.left.toGroupoids)).obj A.obj).obj.val.map a) := sorry

/-- Underlying sheaf comparison of object-inclusion pullback of the Γ-construction
with `π_U^*` of the equivariant module. -/
private def fromPreQuotient_piStar_objIso (A : G.QCoh) :
    ((pullback (SmallQuotient.atlasToPreQuotient G)).obj ((fromPreQuotient G).obj A)).obj ≅
      ((piStar ((Bicategory.Equivalence.id G.U.left.toGroupoids))).obj A.obj).obj :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun y ↦ fromPreQuotient_piStar_evalIso G A y)
      (fun {_ _} a => fromPreQuotient_piStar_objIso_laws G A a))

/-- Components of `fromPreQuotient_piStar_objIso` are `fromPreQuotient_piStar_evalIso`. -/
private theorem fromPreQuotient_piStar_objIso_hom_app (A : G.QCoh)
    (y : (objectGroupoids G).totalᵒᵖ) :
    (fromPreQuotient_piStar_objIso G A).hom.val.app y =
      (fromPreQuotient_piStar_evalIso G A y).hom :=
  rfl

/-- Object-inclusion pullback of the Γ-sheaf identifies with `π_U^*` of the
equivariant module. -/
private def fromPreQuotient_piStarIso (A : G.QCoh) :
    (pullback (SmallQuotient.atlasToPreQuotient G)).obj ((fromPreQuotient G).obj A) ≅
      (piStar ((Bicategory.Equivalence.id G.U.left.toGroupoids))).obj A.obj :=
  (quasiCoherentModuleProperty (objectGroupoids G)).isoMk
    (fromPreQuotient_piStar_objIso G A)

/-- Restriction of the prequotient Γ-sheaf along the object inclusion recovers the
underlying module of an equivariant object, by the `π_U^* ⊣ π_{U,*}` unit after
the Γ-to-`piStar` comparison. -/
def restrict_fromPreQuotientIso (A : G.QCoh) :
    (restrict ((Bicategory.Equivalence.id G.U.left.toGroupoids))).obj
        ((pullback (SmallQuotient.atlasToPreQuotient G)).obj ((fromPreQuotient G).obj A)) ≅
      A.obj :=
  (restrict ((Bicategory.Equivalence.id G.U.left.toGroupoids))).mapIso (fromPreQuotient_piStarIso G A) ≪≫
    (restrict_piStarIso ((Bicategory.Equivalence.id G.U.left.toGroupoids))).symm.app A.obj

/-- `π_U^*` of the atlas restriction of `F` identifies with atlas pullback of `F`,
by the `π_U^* ⊣ π_{U,*}` counit. -/
private def toGroupoid_piStar_atlasIso (F : QCoh (SmallQuotient.quotientStack G)) :
    (piStar ((Bicategory.Equivalence.id G.U.left.toGroupoids))).obj (atlasRestrict G F) ≅
      (pullback (SmallQuotient.atlas G)).obj F :=
  (piStar_restrictIso ((Bicategory.Equivalence.id G.U.left.toGroupoids))).app ((pullback (SmallQuotient.atlas G)).obj F)

/-- Atlas pullback of `F` identifies with object-inclusion pullback of stackification
pullback, by the atlas factorization. -/
private def atlas_stackificationIso (F : QCoh (SmallQuotient.quotientStack G)) :
    (pullback (SmallQuotient.atlas G)).obj F ≅
      (pullback (SmallQuotient.atlasToPreQuotient G)).obj ((pullback (SmallQuotient.stackificationHom G)).obj F) :=
  eqToIso (congrArg (fun h ↦ (pullback h).obj F) (SmallQuotient.atlas_eq G)) ≪≫
    (pullback_comp (SmallQuotient.atlasToPreQuotient G) (SmallQuotient.stackificationHom G)).app F

/-- After object-inclusion pullback, the Γ-construction of `toGroupoid F` identifies
with stackification pullback of `F`. -/
private def toGroupoid_fromPreQuotient_pullbackIso (F : QCoh (SmallQuotient.quotientStack G)) :
    (pullback (SmallQuotient.atlasToPreQuotient G)).obj ((fromPreQuotient G).obj ((toGroupoid G).obj F)) ≅
      (pullback (SmallQuotient.atlasToPreQuotient G)).obj ((pullback (SmallQuotient.stackificationHom G)).obj F) :=
  fromPreQuotient_piStarIso G ((toGroupoid G).obj F) ≪≫
    toGroupoid_piStar_atlasIso G F ≪≫ atlas_stackificationIso G F

/-- Underlying sheaf morphism of `toGroupoid_fromPreQuotient_pullbackIso`. -/
private def toGroupoid_fromPreQuotient_pullbackModulesHom (F : QCoh (SmallQuotient.quotientStack G)) :
    ((pullback (SmallQuotient.atlasToPreQuotient G)).obj ((fromPreQuotient G).obj ((toGroupoid G).obj F))).obj ⟶
      ((pullback (SmallQuotient.atlasToPreQuotient G)).obj ((pullback (SmallQuotient.stackificationHom G)).obj F)).obj :=
  (toGroupoid_fromPreQuotient_pullbackIso G F).hom.hom

/-- Underlying inverse sheaf morphism of `toGroupoid_fromPreQuotient_pullbackIso`. -/
private def toGroupoid_fromPreQuotient_pullbackModulesInv (F : QCoh (SmallQuotient.quotientStack G)) :
    ((pullback (SmallQuotient.atlasToPreQuotient G)).obj ((pullback (SmallQuotient.stackificationHom G)).obj F)).obj ⟶
      ((pullback (SmallQuotient.atlasToPreQuotient G)).obj ((fromPreQuotient G).obj ((toGroupoid G).obj F))).obj :=
  (toGroupoid_fromPreQuotient_pullbackIso G F).inv.hom

/-- Restriction-of-scalars comparison of the Γ-construction at the image of
`objectPoint` with object-inclusion pullback. -/
private def fromPreQuotient_modulePullback_evalIso (A : G.QCoh) (x : (SmallQuotient.preQuotient G).total) :
    ((modulePullback (SmallQuotient.atlasToPreQuotient G)).obj
          ((fromPreQuotient G).obj A).obj).val.obj (op (objectPoint G x)) ≅
      (ModuleCat.restrictScalars
          ((structureSheafMap (SmallQuotient.atlasToPreQuotient G)).hom.app
            (op (objectPoint G x))).hom).obj
        (((fromPreQuotient G).obj A).obj.val.obj (op (atlasToPreQuotientObj G (objectPoint G x)))) :=
  modulePullback_evalIso (SmallQuotient.atlasToPreQuotient G) ((fromPreQuotient G).obj A).obj
    (objectPoint G x)

/-- Restriction-of-scalars comparison of stackification pullback at the image of
`objectPoint` with evaluation at the image object. -/
private def stackification_modulePullback_evalIso (F : QCoh (SmallQuotient.quotientStack G))
    (x : (SmallQuotient.preQuotient G).total) :
    ((modulePullback (SmallQuotient.atlasToPreQuotient G)).obj
          ((pullback (SmallQuotient.stackificationHom G)).obj F).obj).val.obj
        (op (objectPoint G x)) ≅
      (ModuleCat.restrictScalars
          ((structureSheafMap (SmallQuotient.atlasToPreQuotient G)).hom.app
            (op (objectPoint G x))).hom).obj
        (((pullback (SmallQuotient.stackificationHom G)).obj F).obj.val.obj (op (atlasToPreQuotientObj G (objectPoint G x)))) :=
  modulePullback_evalIso (SmallQuotient.atlasToPreQuotient G)
    ((pullback (SmallQuotient.stackificationHom G)).obj F).obj (objectPoint G x)

/-- The morphism of restricted-scalar modules at `objectPoint` induced by
`toGroupoid_fromPreQuotient_pullbackModulesHom`. -/
private def toGroupoid_fromPreQuotient_restrictedHom (F : QCoh (SmallQuotient.quotientStack G))
    (x : (SmallQuotient.preQuotient G).total) :
    (ModuleCat.restrictScalars
        ((structureSheafMap (SmallQuotient.atlasToPreQuotient G)).hom.app
          (op (objectPoint G x))).hom).obj
      (((toGroupoid G ⋙ fromPreQuotient G).obj F).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x)))) ⟶
    (ModuleCat.restrictScalars
        ((structureSheafMap (SmallQuotient.atlasToPreQuotient G)).hom.app
          (op (objectPoint G x))).hom).obj
      (((pullback (SmallQuotient.stackificationHom G)).obj F).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x)))) :=
  (fromPreQuotient_modulePullback_evalIso G ((toGroupoid G).obj F) x).inv ≫
    (pullback_compιIso (SmallQuotient.atlasToPreQuotient G)
        ((fromPreQuotient G).obj ((toGroupoid G).obj F))).inv.val.app
      (op (objectPoint G x)) ≫
    (toGroupoid_fromPreQuotient_pullbackModulesHom G F).val.app
      (op (objectPoint G x)) ≫
    (pullback_compιIso (SmallQuotient.atlasToPreQuotient G)
        ((pullback (SmallQuotient.stackificationHom G)).obj F)).hom.val.app
      (op (objectPoint G x)) ≫
    (stackification_modulePullback_evalIso G F x).hom

/-- Inverse of `toGroupoid_fromPreQuotient_restrictedHom`. -/
private def toGroupoid_fromPreQuotient_restrictedInv (F : QCoh (SmallQuotient.quotientStack G))
    (x : (SmallQuotient.preQuotient G).total) :
    (ModuleCat.restrictScalars
        ((structureSheafMap (SmallQuotient.atlasToPreQuotient G)).hom.app
          (op (objectPoint G x))).hom).obj
      (((pullback (SmallQuotient.stackificationHom G)).obj F).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x)))) ⟶
    (ModuleCat.restrictScalars
        ((structureSheafMap (SmallQuotient.atlasToPreQuotient G)).hom.app
          (op (objectPoint G x))).hom).obj
      (((toGroupoid G ⋙ fromPreQuotient G).obj F).obj.val.obj
        (op (atlasToPreQuotientObj G (objectPoint G x)))) :=
  (stackification_modulePullback_evalIso G F x).inv ≫
    (pullback_compιIso (SmallQuotient.atlasToPreQuotient G)
        ((pullback (SmallQuotient.stackificationHom G)).obj F)).inv.val.app
      (op (objectPoint G x)) ≫
    (toGroupoid_fromPreQuotient_pullbackModulesInv G F).val.app
      (op (objectPoint G x)) ≫
    (pullback_compιIso (SmallQuotient.atlasToPreQuotient G)
        ((fromPreQuotient G).obj ((toGroupoid G).obj F))).hom.val.app
      (op (objectPoint G x)) ≫
    (fromPreQuotient_modulePullback_evalIso G ((toGroupoid G).obj F) x).hom

/-- Objectwise forward map of the Γ-construction of `toGroupoid F` toward
stackification pullback of `F`, by object transport along
`atlasToPreQuotient_objectPoint` and restriction of scalars along the
isomorphism `structureSheafMap`. -/
private def toGroupoid_fromPreQuotient_app (F : QCoh (SmallQuotient.quotientStack G))
    (x : (SmallQuotient.preQuotient G).totalᵒᵖ) :
    ((toGroupoid G ⋙ fromPreQuotient G).obj F).obj.val.obj x ⟶
      ((pullback (SmallQuotient.stackificationHom G)).obj F).obj.val.obj x :=
  fromPreQuotient_objectPoint_eqToHom_inv G ((toGroupoid G).obj F) x.unop ≫
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (structureSheafMap_appRingEquiv (SmallQuotient.atlasToPreQuotient G)
        (op (objectPoint G x.unop)))).fullyFaithfulFunctor.preimage
      (toGroupoid_fromPreQuotient_restrictedHom G F x.unop) ≫
    stackification_objectPoint_eqToHom G F x.unop

/-- Objectwise inverse map of stackification pullback of `F` toward the
Γ-construction of `toGroupoid F`. -/
private def toGroupoid_fromPreQuotient_app_inv (F : QCoh (SmallQuotient.quotientStack G))
    (x : (SmallQuotient.preQuotient G).totalᵒᵖ) :
    ((pullback (SmallQuotient.stackificationHom G)).obj F).obj.val.obj x ⟶
      ((toGroupoid G ⋙ fromPreQuotient G).obj F).obj.val.obj x :=
  stackification_objectPoint_eqToHom_inv G F x.unop ≫
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (structureSheafMap_appRingEquiv (SmallQuotient.atlasToPreQuotient G)
        (op (objectPoint G x.unop)))).fullyFaithfulFunctor.preimage
      (toGroupoid_fromPreQuotient_restrictedInv G F x.unop) ≫
    fromPreQuotient_objectPoint_eqToHom G ((toGroupoid G).obj F) x.unop

/-- The prestack comparison components and their inverses commute with
restriction and satisfy both inverse identities. -/
private theorem toGroupoid_comp_fromPreQuotient_objIso_laws
    (F : QCoh (SmallQuotient.quotientStack G)) :
    let M := ((toGroupoid G ⋙ fromPreQuotient G).obj F).obj.val
    let N := ((pullback (SmallQuotient.stackificationHom G)).obj F).obj.val
    (∀ {x y} (a : x ⟶ y), M.map a ≫
      (ModuleCat.restrictScalars ((structureSheaf (SmallQuotient.preQuotient G)).obj.map a).hom).map
        (toGroupoid_fromPreQuotient_app G F y) =
      toGroupoid_fromPreQuotient_app G F x ≫ N.map a) ∧
    (∀ {x y} (a : x ⟶ y), N.map a ≫
      (ModuleCat.restrictScalars ((structureSheaf (SmallQuotient.preQuotient G)).obj.map a).hom).map
        (toGroupoid_fromPreQuotient_app_inv G F y) =
      toGroupoid_fromPreQuotient_app_inv G F x ≫ M.map a) ∧
    (∀ x, toGroupoid_fromPreQuotient_app G F x ≫ toGroupoid_fromPreQuotient_app_inv G F x = 𝟙 _) ∧
    (∀ x, toGroupoid_fromPreQuotient_app_inv G F x ≫ toGroupoid_fromPreQuotient_app G F x = 𝟙 _) := sorry

/-- Underlying sheaf comparison of `fromPreQuotient (toGroupoid F)` with
stackification pullback. -/
private def toGroupoid_comp_fromPreQuotient_objIso (F : QCoh (SmallQuotient.quotientStack G)) :
    ((toGroupoid G ⋙ fromPreQuotient G).obj F).obj ≅
      ((pullback (SmallQuotient.stackificationHom G)).obj F).obj where
  hom :=
    { val :=
        { app := fun x ↦ toGroupoid_fromPreQuotient_app G F x
          naturality := (toGroupoid_comp_fromPreQuotient_objIso_laws G F).1 } }
  inv :=
    { val :=
        { app := fun x ↦ toGroupoid_fromPreQuotient_app_inv G F x
          naturality := (toGroupoid_comp_fromPreQuotient_objIso_laws G F).2.1 } }
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    exact fun x => (toGroupoid_comp_fromPreQuotient_objIso_laws G F).2.2.1 x
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    exact fun x => (toGroupoid_comp_fromPreQuotient_objIso_laws G F).2.2.2 x

/-- Reconstruction of atlas restriction commutes with morphisms on the quotient stack. -/
private theorem toGroupoid_comp_fromPreQuotient_laws
    {F F' : QCoh (SmallQuotient.quotientStack G)} (f : F ⟶ F') :
    (toGroupoid G ⋙ fromPreQuotient G).map f ≫
        (quasiCoherentModuleProperty (SmallQuotient.preQuotient G)).homMk
          (toGroupoid_comp_fromPreQuotient_objIso G F').hom =
      (quasiCoherentModuleProperty (SmallQuotient.preQuotient G)).homMk
          (toGroupoid_comp_fromPreQuotient_objIso G F).hom ≫
        (pullback (SmallQuotient.stackificationHom G)).map f := sorry

/-- `toGroupoid` followed by the prequotient Γ-construction is pullback along
stackification. -/
private def toGroupoid_comp_fromPreQuotient :
    toGroupoid G ⋙ fromPreQuotient G ≅ pullback (SmallQuotient.stackificationHom G) :=
  NatIso.ofComponents
    (fun F ↦
      (quasiCoherentModuleProperty (SmallQuotient.preQuotient G)).isoMk
        (toGroupoid_comp_fromPreQuotient_objIso G F))
    (fun f => toGroupoid_comp_fromPreQuotient_laws G f)

/-- The unit identification of `toGroupoid` followed by `QuotientQCoh.fromGroupoidStack`, obtained
from stackification pullback and the Γ-description of the prequotient inverse. -/
def toGroupoidEquivalence_unitIso :
    𝟭 (QCoh (SmallQuotient.quotientStack G)) ≅ toGroupoid G ⋙ QuotientQCoh.fromGroupoidStack G :=
  let E := LocalEquivalenceModules.qcohEquivalence (SmallQuotient.stackificationHom G)
    (FiberedCategoryOver.Groupoids.Hom.IsStackification.isLocalEquivalence
      (SmallQuotient.stackificationHom_isStackification G))
  E.unitIso ≪≫
    Functor.isoWhiskerRight (toGroupoid_comp_fromPreQuotient G).symm E.inverse ≪≫
      (Functor.associator (toGroupoid G) (fromPreQuotient G) E.inverse).symm

/-- Atlas pullback of `QuotientQCoh.fromGroupoidStack A` identifies with object-inclusion pullback of
the prequotient Γ-sheaf, via stackification. -/
private def fromGroupoid_atlasPullbackIso (A : G.QCoh) :
    (pullback (SmallQuotient.atlas G)).obj ((QuotientQCoh.fromGroupoidStack G).obj A) ≅
      (pullback (SmallQuotient.atlasToPreQuotient G)).obj ((fromPreQuotient G).obj A) :=
  eqToIso (congrArg (fun h ↦ (pullback h).obj ((QuotientQCoh.fromGroupoidStack G).obj A)) (SmallQuotient.atlas_eq G)) ≪≫
    (pullback_comp (SmallQuotient.atlasToPreQuotient G) (SmallQuotient.stackificationHom G)).app ((QuotientQCoh.fromGroupoidStack G).obj A) ≪≫
    (pullback (SmallQuotient.atlasToPreQuotient G)).mapIso ((QuotientQCoh.fromGroupoidStack_comp_pullback G).app A)

/-- The underlying module of `toGroupoid (QuotientQCoh.fromGroupoidStack A)` identifies with the
underlying module of `A`. -/
private def fromGroupoid_toGroupoid_objIso (A : G.QCoh) :
    GroupoidAlgebraicSpace.QCoh.obj ((toGroupoid G).obj ((QuotientQCoh.fromGroupoidStack G).obj A)) ≅
      A.obj :=
  (restrict ((Bicategory.Equivalence.id G.U.left.toGroupoids))).mapIso (fromGroupoid_atlasPullbackIso G A) ≪≫
    restrict_fromPreQuotientIso G A

/-- The reconstructed atlas comparison is equivariant in both directions
and natural in the equivariant module. -/
private theorem toGroupoidEquivalence_counitIso_laws :
    (∀ A : G.QCoh,
      (AlgebraicSpace.QCoh.pullback G.t.left).map (fromGroupoid_toGroupoid_objIso G A).hom ≫ A.action =
        ((toGroupoid G).obj ((QuotientQCoh.fromGroupoidStack G).obj A)).action ≫
          (AlgebraicSpace.QCoh.pullback G.s.left).map (fromGroupoid_toGroupoid_objIso G A).hom) ∧
    (∀ A : G.QCoh,
      (AlgebraicSpace.QCoh.pullback G.t.left).map (fromGroupoid_toGroupoid_objIso G A).inv ≫
        ((toGroupoid G).obj ((QuotientQCoh.fromGroupoidStack G).obj A)).action =
      A.action ≫ (AlgebraicSpace.QCoh.pullback G.s.left).map (fromGroupoid_toGroupoid_objIso G A).inv) ∧
    (∀ {A A' : G.QCoh} (f : A ⟶ A'),
      GroupoidAlgebraicSpace.QCoh.hom ((QuotientQCoh.fromGroupoidStack G ⋙ toGroupoid G).map f) ≫
        (fromGroupoid_toGroupoid_objIso G A').hom =
      (fromGroupoid_toGroupoid_objIso G A).hom ≫ GroupoidAlgebraicSpace.QCoh.hom f) := sorry

/-- The counit identification of `QuotientQCoh.fromGroupoidStack` followed by `toGroupoid`. -/
def toGroupoidEquivalence_counitIso :
    QuotientQCoh.fromGroupoidStack G ⋙ toGroupoid G ≅ 𝟭 G.QCoh :=
  NatIso.ofComponents
    (fun A ↦
      { hom :=
          System.Hom.of
            (fromGroupoid_toGroupoid_objIso G A).hom
            ((toGroupoidEquivalence_counitIso_laws G).1 A)
        inv :=
          System.Hom.of
            (fromGroupoid_toGroupoid_objIso G A).inv
            ((toGroupoidEquivalence_counitIso_laws G).2.1 A)
        hom_inv_id := System.Hom.ext (fromGroupoid_toGroupoid_objIso G A).hom_inv_id
        inv_hom_id := System.Hom.ext (fromGroupoid_toGroupoid_objIso G A).inv_hom_id })
    (fun f => System.Hom.ext ((toGroupoidEquivalence_counitIso_laws G).2.2 f))

/-- Quasi-coherent modules on a quotient stack are equivalent to equivariant
quasi-coherent modules on its groupoid presentation. -/
def toGroupoidEquivalence : QCoh (SmallQuotient.quotientStack G) ≌ G.QCoh :=
  CategoryTheory.Equivalence.mk (toGroupoid G) (QuotientQCoh.fromGroupoidStack G)
    (toGroupoidEquivalence_unitIso G) (toGroupoidEquivalence_counitIso G)

/-- `toGroupoidEquivalence` is the functor `toGroupoid`. -/
theorem toGroupoidEquivalence_functor :
    (toGroupoidEquivalence G).functor = toGroupoid G :=
  rfl

/-- `toGroupoidEquivalence` has specified inverse `QuotientQCoh.fromGroupoidStack`. -/
theorem toGroupoidEquivalence_inverse :
    (toGroupoidEquivalence G).inverse = QuotientQCoh.fromGroupoidStack G :=
  rfl

end AlgebraicGeometry.GroupoidsOver.QCoh
