/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ModuleDescent
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.LowerShriek

/-!
# Equivalence between cartesian modules and face-descent data

Cartesian `O`-modules on `C_total` are equivalent to pairs `(F, α)` of an `O_0`-module
and an `O_1`-module isomorphism satisfying the `O_2` cocycle.
-/

-- Public constructions expose their concrete bodies while section maps and proof laws stay private.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites.Module

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram.{u, v, w} C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]
include instMorphismDiagram instWeakSheafify instLeftKan

/-- The object property of being a cartesian `O`-module on `C_total`. -/
abbrev cartesianProperty :
    ObjectProperty (SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :=
  fun F ↦ IsCartesian C J O F

/-- The category of cartesian `O`-modules on `C_total`. -/
abbrev Cartesian := (cartesianProperty C J O).FullSubcategory

/-- The two coface transition isomorphisms of a cartesian module satisfy the cocycle. -/
private theorem toDescent_cocycle (F : Cartesian C J O) :
    cocycleLeft C J O
      ((@transitionIso C J _ _ _ O _ _ _ _ _ _ _ F.obj F.property _ _
          (SimplexCategory.δ (1 : Fin 2))) ≪≫
        (@transitionIso C J _ _ _ O _ _ _ _ _ _ _ F.obj F.property _ _
          (SimplexCategory.δ (0 : Fin 2))).symm) =
    cocycleRight C J O
      ((@transitionIso C J _ _ _ O _ _ _ _ _ _ _ F.obj F.property _ _
          (SimplexCategory.δ (1 : Fin 2))) ≪≫
        (@transitionIso C J _ _ _ O _ _ _ _ _ _ _ F.obj F.property _ _
          (SimplexCategory.δ (0 : Fin 2))).symm) := sorry

/-- Extract the degree-zero module and the comparison of its two coface pullbacks. -/
def toDescent (F : Cartesian C J O) : FaceDescent C J O :=
  FaceDescent.ofIso ((moduleComponent C J O ⦋0⦌).obj F.obj)
    ((@transitionIso C J _ _ _ O _ _ _ _ _ _ _ F.obj F.property _ _
        (SimplexCategory.δ (1 : Fin 2))) ≪≫
      (@transitionIso C J _ _ _ O _ _ _ _ _ _ _ F.obj F.property _ _
        (SimplexCategory.δ (0 : Fin 2))).symm)
    (toDescent_cocycle C J O F)

/-- The extracted module is the degree-zero component. -/
theorem toDescent_module (F : Cartesian C J O) :
    (toDescent C J O F).module = (moduleComponent C J O ⦋0⦌).obj F.obj := rfl

/-- Ring identification `O_n(obj U) ⟶ O(U)` from `U = ofObj (degree U) (obj U)`. -/
private def componentRingEval (U : totalSite C) :
    (componentRingedSite C J O (degree U)).structureSheaf.obj.obj (op (obj U)) ⟶
      (totalRingedSite C J O).structureSheaf.obj.obj (op U) :=
  (totalRingedSite C J O).structureSheaf.obj.map (eqToHom (rfl : U = ofObj C (degree U) (obj U))).op

/-- Evaluation of `(f_{τ^{deg U}_{deg U}})^* F` at `obj U`. -/
private def vertexPullbackEval (D : FaceDescent C J O) (U : totalSite C) :
    ModuleCat.{w}
      ((componentRingedSite C J O (degree U)).structureSheaf.obj.obj (op (obj U))) :=
  ((ringedToposMap C J O (vertexOp (degree U))).modulePullback.obj D.module).val.obj
    (op (obj U))

/-- Sections of the reconstructed module over `U`, as an `O(U)`-module. -/
private def ofDescentObj (D : FaceDescent C J O) (U : totalSite C) :
    ModuleCat.{w} ((totalRingedSite C J O).structureSheaf.obj.obj (op U)) :=
  (ModuleCat.restrictScalars (componentRingEval C J O U).hom).obj
    (vertexPullbackEval C J O D U)

/-- Direct-image mate of `transitionOf φ D`, as an `O_n`-module map. -/
private def transitionOfMate {n m : SimplexCategory} (φ : n ⟶ m) (D : FaceDescent C J O) :
    (ringedToposMap C J O (vertexOp n)).modulePullback.obj D.module ⟶
      (ringedToposMap C J O φ).modulePushforward.obj
        ((ringedToposMap C J O (vertexOp m)).modulePullback.obj D.module) :=
  ((ringedToposMap C J O φ).moduleAdjunction.homEquiv
      ((ringedToposMap C J O (vertexOp n)).modulePullback.obj D.module)
      ((ringedToposMap C J O (vertexOp m)).modulePullback.obj D.module))
    (FaceDescent.transitionOf φ D)

/-- Underlying function of module pushforward evaluation along `u_φ`. -/
private def modulePushforwardEvalFun {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (componentRingedSite C J O n).structureSheaf) (U : C.obj m) :
    ((ringedToposMap C J O φ).modulePushforward.obj M).val.obj (op U) →
      M.val.obj (op ((C.map φ).toFunctor.obj U)) :=
  fun x ↦
    ((ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O φ)).hom.app M).hom.app
      (op U) x

/-- Underlying restriction of a reconstructed module along a total-category morphism `(φ, g)`. -/
private def ofDescentMapFun (D : FaceDescent C J O) {U V : totalSite C} (η : U ⟶ V)
    (x : vertexPullbackEval C J O D V) : vertexPullbackEval C J O D U :=
  (((ringedToposMap C J O (vertexOp (degree U))).modulePullback.obj D.module).val.map
      (homToPair η).2.op)
    (modulePushforwardEvalFun C J O (homToPair η).1
      ((ringedToposMap C J O (vertexOp (degree U))).modulePullback.obj D.module)
      (obj V)
      ((transitionOfMate C J O (homToPair η).1 D).val.app (op (obj V)) x))

/-- Total-site restriction functions preserve addition and the transported scalar action. -/
private theorem ofDescentValMap_linear (D : FaceDescent C J O)
    {W Z : (totalSite C)ᵒᵖ} (η : W ⟶ Z) :
    (∀ x y : ofDescentObj C J O D W.unop,
      ofDescentMapFun C J O D η.unop (x + y) =
        ofDescentMapFun C J O D η.unop x + ofDescentMapFun C J O D η.unop y) ∧
    (∀ (r : (totalRingedSite C J O).structureSheaf.obj.obj W)
      (x : ofDescentObj C J O D W.unop),
      ofDescentMapFun C J O D η.unop (r • x) =
        @SMul.smul _ _ (ofDescentObj C J O D Z.unop).isModule.toSMul
          (((totalRingedSite C J O).structureSheaf.obj.map η) r)
          (ofDescentMapFun C J O D η.unop x)) := sorry

/-- Restriction of a reconstructed module along a total-category morphism, as an `O`-linear
map. -/
private def ofDescentValMap (D : FaceDescent C J O) {W Z : (totalSite C)ᵒᵖ} (η : W ⟶ Z) :
    ofDescentObj C J O D W.unop ⟶
      (ModuleCat.restrictScalars
        ((totalRingedSite C J O).structureSheaf.obj.map η).hom).obj
        (ofDescentObj C J O D Z.unop) :=
  @ModuleCat.ofHom _ _ (ofDescentObj C J O D W.unop) ((ModuleCat.restrictScalars
        ((totalRingedSite C J O).structureSheaf.obj.map η).hom).obj
        (ofDescentObj C J O D Z.unop))
    (ofDescentObj C J O D W.unop).isAddCommGroup (ofDescentObj C J O D W.unop).isModule
    ((ModuleCat.restrictScalars
        ((totalRingedSite C J O).structureSheaf.obj.map η).hom).obj
        (ofDescentObj C J O D Z.unop)).isAddCommGroup ((ModuleCat.restrictScalars
        ((totalRingedSite C J O).structureSheaf.obj.map η).hom).obj
        (ofDescentObj C J O D Z.unop)).isModule
    { toFun := fun x ↦ ofDescentMapFun C J O D η.unop x
      map_add' := (ofDescentValMap_linear C J O D η).1
      map_smul' := (ofDescentValMap_linear C J O D η).2 }

/-- The specified total-site restriction maps preserve identities and composition. -/
private theorem ofDescentPresheaf_laws (D : FaceDescent C J O) :
    let R := (totalRingedSite C J O).structureSheaf.obj
    (∀ W : (totalSite C)ᵒᵖ,
      ofDescentValMap C J O D (𝟙 W) =
        (ModuleCat.restrictScalarsId' (R.map (𝟙 W)).hom
          (congrArg RingCat.Hom.hom (R.map_id W))).inv.app
            (ofDescentObj C J O D W.unop)) ∧
    (∀ {W X Y : (totalSite C)ᵒᵖ} (f : W ⟶ X) (g : X ⟶ Y),
      ofDescentValMap C J O D (f ≫ g) =
        ofDescentValMap C J O D f ≫
          (ModuleCat.restrictScalars (R.map f).hom).map (ofDescentValMap C J O D g) ≫
          (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
            (congrArg RingCat.Hom.hom (R.map_comp f g))).inv.app
              (ofDescentObj C J O D Y.unop)) := sorry

/-- The presheaf assembled from last-vertex sections and their canonical restriction maps. -/
private def ofDescentPresheaf (D : FaceDescent C J O) :
    PresheafOfModules.{w} (totalRingedSite C J O).structureSheaf.obj where
  obj W := ofDescentObj C J O D W.unop
  map η := ofDescentValMap C J O D η
  map_id := (ofDescentPresheaf_laws C J O D).1
  map_comp := (ofDescentPresheaf_laws C J O D).2

/-- Last-vertex reconstruction satisfies the sheaf condition on the total site. -/
private theorem ofDescent_isSheaf (D : FaceDescent C J O) :
    Presheaf.IsSheaf (topology C J) (ofDescentPresheaf C J O D).presheaf := sorry

/-- Assemble a sheaf of `O`-modules on `C_total` from a face-descent pair. -/
def ofDescent (D : FaceDescent C J O) :
    SheafOfModules.{w} (totalRingedSite C J O).structureSheaf where
  val := ofDescentPresheaf C J O D
  isSheaf := ofDescent_isSheaf C J O D

/-- Reconstructed sections are the last-vertex pullback sections with the total-site scalars. -/
theorem ofDescent_obj_app (D : FaceDescent C J O) (U : totalSite C) :
    (ofDescent C J O D).val.obj (op U) =
      (ModuleCat.restrictScalars
        ((totalRingedSite C J O).structureSheaf.obj.map
          (eqToHom (rfl : U = ofObj C (degree U) (obj U))).op).hom).obj
        (((ringedToposMap C J O (vertexOp (degree U))).modulePullback.obj D.module).val.obj
          (op (obj U))) := rfl

/-- Pullback morphisms on last-vertex sections are linear for total-site scalars. -/
private theorem ofDescentMapApp_linear {D E : FaceDescent C J O}
    (α : FaceDescent.Hom D E) (W : (totalSite C)ᵒᵖ) :
    (∀ x y : (ofDescent C J O D).val.obj W,
      ((ringedToposMap C J O (vertexOp (degree W.unop))).modulePullback.map α.hom).val.app
          (op (obj W.unop)) (x + y) =
        ((ringedToposMap C J O (vertexOp (degree W.unop))).modulePullback.map α.hom).val.app
          (op (obj W.unop)) x +
        ((ringedToposMap C J O (vertexOp (degree W.unop))).modulePullback.map α.hom).val.app
          (op (obj W.unop)) y) ∧
    (∀ (r : (totalRingedSite C J O).structureSheaf.obj.obj W)
      (x : (ofDescent C J O D).val.obj W),
      ((ringedToposMap C J O (vertexOp (degree W.unop))).modulePullback.map α.hom).val.app
          (op (obj W.unop)) (r • x) =
        @SMul.smul _ _ ((ofDescent C J O E).val.obj W).isModule.toSMul r
          (((ringedToposMap C J O (vertexOp (degree W.unop))).modulePullback.map
            α.hom).val.app (op (obj W.unop)) x)) := sorry

/-- The linear map on sections induced by a morphism of descent pairs. -/
private def ofDescentMapApp {D E : FaceDescent C J O} (α : FaceDescent.Hom D E)
    (W : (totalSite C)ᵒᵖ) :
    (ofDescent C J O D).val.obj W ⟶ (ofDescent C J O E).val.obj W :=
  @ModuleCat.ofHom _ _ ((ofDescent C J O D).val.obj W) ((ofDescent C J O E).val.obj W)
    ((ofDescent C J O D).val.obj W).isAddCommGroup ((ofDescent C J O D).val.obj W).isModule
    ((ofDescent C J O E).val.obj W).isAddCommGroup ((ofDescent C J O E).val.obj W).isModule
    { toFun := fun x ↦
        ((ringedToposMap C J O (vertexOp (degree W.unop))).modulePullback.map
          α.hom).val.app (op (obj W.unop)) x
      map_add' := (ofDescentMapApp_linear C J O α W).1
      map_smul' := (ofDescentMapApp_linear C J O α W).2 }

/-- The reconstructed component maps commute with restriction. -/
private theorem ofDescentMap_naturality {D E : FaceDescent C J O}
    (α : FaceDescent.Hom D E) {W Z : (totalSite C)ᵒᵖ} (η : W ⟶ Z) :
    (ofDescent C J O D).val.map η ≫
        (ModuleCat.restrictScalars ((totalRingedSite C J O).structureSheaf.obj.map η).hom).map
          (ofDescentMapApp C J O α Z) =
      ofDescentMapApp C J O α W ≫ (ofDescent C J O E).val.map η := sorry

/-- A morphism of descent pairs induces a morphism of reconstructed module sheaves. -/
def ofDescentMap {D E : FaceDescent C J O} (α : FaceDescent.Hom D E) :
    ofDescent C J O D ⟶ ofDescent C J O E where
  val :=
    { app := ofDescentMapApp C J O α
      naturality := ofDescentMap_naturality C J O α }

/-- Degree-zero restriction of a cartesian-module morphism respects the coface comparisons. -/
private theorem toDescentMap_comm {F G : Cartesian C J O} (f : F ⟶ G) :
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map
        ((moduleComponent C J O ⦋0⦌).map f.hom) ≫ (toDescent C J O G).iso.hom =
      (toDescent C J O F).iso.hom ≫
        (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map
          ((moduleComponent C J O ⦋0⦌).map f.hom) := sorry

/-- Degree-zero restriction as a morphism of descent pairs. -/
private def toDescentMap {F G : Cartesian C J O} (f : F ⟶ G) :
    toDescent C J O F ⟶ toDescent C J O G :=
  FaceDescent.homMk ((moduleComponent C J O ⦋0⦌).map f.hom) (toDescentMap_comm C J O f)

/-- Extraction preserves identity morphisms and composition. -/
private theorem toDescentFunctor_laws :
    (∀ F : Cartesian C J O, toDescentMap C J O (𝟙 F) = 𝟙 (toDescent C J O F)) ∧
    (∀ {F G H : Cartesian C J O} (f : F ⟶ G) (g : G ⟶ H),
      toDescentMap C J O (f ≫ g) = toDescentMap C J O f ≫ toDescentMap C J O g) := sorry

/-- The functor extracting the degree-zero module and its coface comparison. -/
def toDescentFunctor : Cartesian C J O ⥤ FaceDescent C J O where
  obj F := toDescent C J O F
  map f := toDescentMap C J O f
  map_id := (toDescentFunctor_laws C J O).1
  map_comp := (toDescentFunctor_laws C J O).2

/-- Extraction on objects is the prescribed degree-zero descent pair. -/
theorem toDescentFunctor_obj (F : Cartesian C J O) :
    (toDescentFunctor C J O).obj F = toDescent C J O F := rfl

/-- Last-vertex reconstruction is cartesian for every simplex operator. -/
private theorem ofDescent_isCartesian (D : FaceDescent C J O) :
    IsCartesian C J O (ofDescent C J O D) := sorry

/-- Reconstruction preserves identity morphisms and composition. -/
private theorem ofDescentFunctor_laws :
    (∀ D : FaceDescent C J O, ofDescentMap C J O (𝟙 D) = 𝟙 (ofDescent C J O D)) ∧
    (∀ {D E F : FaceDescent C J O} (f : D ⟶ E) (g : E ⟶ F),
      ofDescentMap C J O (f ≫ g) = ofDescentMap C J O f ≫ ofDescentMap C J O g) := sorry

/-- The functor reconstructing a cartesian module from a coface descent pair. -/
def ofDescentFunctor : FaceDescent C J O ⥤ Cartesian C J O where
  obj D := ⟨ofDescent C J O D, ofDescent_isCartesian C J O D⟩
  map α := ObjectProperty.homMk (ofDescentMap C J O α)
  map_id D := by
    apply ObjectProperty.hom_ext
    exact (ofDescentFunctor_laws C J O).1 D
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (ofDescentFunctor_laws C J O).2 f g

/-- The underlying reconstructed module is the prescribed last-vertex assembly. -/
theorem ofDescentFunctor_obj_obj (D : FaceDescent C J O) :
    ((ofDescentFunctor C J O).obj D).obj = ofDescent C J O D := rfl

/-- Underlying type-valued sheaf of an `O`-module on `C_total`. -/
private abbrev totalUnderlying (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    Sheaf (topology C J) (Type w) :=
  (Sheaf.InternalModule.ToInternal.underlying
      (totalRingedSite C J O).structureSheaf).obj F

/-- Component of the unit isomorphism on underlying sections. -/
private def cartesianUnitAppFun (F : Cartesian C J O) (U : totalSite C)
    (x : F.obj.val.obj (op U)) : vertexPullbackEval C J O (toDescent C J O F) U :=
  (@transitionIso C J _ _ _ O _ _ _ _ _ _ _ F.obj F.property _ _ (vertexOp (degree U))).inv.val.app
      (op (obj U))
    ((modulePullback_underlyingIso C J O (degree U) F.obj).inv.hom.app (op (obj U))
      (((ofStage C (degree U)).sheafPushforwardContinuousObjObjIso (Type w)
        (totalUnderlying C J O F.obj) (obj U)).inv
        (F.obj.val.map (eqToHom (rfl : U = ofObj C (degree U) (obj U))).op x)))

/-- Component of the inverse unit isomorphism on underlying sections. -/
private def cartesianUnitAppInvFun (F : Cartesian C J O) (U : totalSite C)
    (x : vertexPullbackEval C J O (toDescent C J O F) U) : F.obj.val.obj (op U) :=
  F.obj.val.map (eqToHom (rfl : U = ofObj C (degree U) (obj U)).symm).op
    (((ofStage C (degree U)).sheafPushforwardContinuousObjObjIso (Type w)
        (totalUnderlying C J O F.obj) (obj U)).hom
      ((modulePullback_underlyingIso C J O (degree U) F.obj).hom.hom.app (op (obj U))
        ((@transitionIso C J _ _ _ O _ _ _ _ _ _ _ F.obj F.property _ _ (vertexOp (degree U))).hom.val.app
          (op (obj U)) x)))

/-- The forward and inverse comparison functions preserve addition and scalar multiplication. -/
private theorem cartesianUnitApp_linear (F : Cartesian C J O) (W : (totalSite C)ᵒᵖ) :
    ((∀ x y : (F.obj).val.obj W,
      cartesianUnitAppFun C J O F W.unop (x + y) =
        cartesianUnitAppFun C J O F W.unop x + cartesianUnitAppFun C J O F W.unop y) ∧
    (∀ (r : (totalRingedSite C J O).structureSheaf.obj.obj W)
      (x : (F.obj).val.obj W),
      cartesianUnitAppFun C J O F W.unop (r • x) =
        @SMul.smul _ _ ((ofDescent C J O (toDescent C J O F)).val.obj W).isModule.toSMul r
          (cartesianUnitAppFun C J O F W.unop x))) ∧
    ((∀ x y : (ofDescent C J O (toDescent C J O F)).val.obj W,
      cartesianUnitAppInvFun C J O F W.unop (x + y) =
        cartesianUnitAppInvFun C J O F W.unop x + cartesianUnitAppInvFun C J O F W.unop y) ∧
    (∀ (r : (totalRingedSite C J O).structureSheaf.obj.obj W)
      (x : (ofDescent C J O (toDescent C J O F)).val.obj W),
      cartesianUnitAppInvFun C J O F W.unop (r • x) =
        @SMul.smul _ _ ((F.obj).val.obj W).isModule.toSMul r
          (cartesianUnitAppInvFun C J O F W.unop x))) := sorry

/-- The hom comparison on sections, bundled as a linear map. -/
private def cartesianUnitAppHom (F : Cartesian C J O) (W : (totalSite C)ᵒᵖ) :
    (F.obj).val.obj W ⟶ (ofDescent C J O (toDescent C J O F)).val.obj W :=
  @ModuleCat.ofHom _ _ (F.obj.val.obj W) ((ofDescent C J O (toDescent C J O F)).val.obj W)
    (F.obj.val.obj W).isAddCommGroup (F.obj.val.obj W).isModule
    ((ofDescent C J O (toDescent C J O F)).val.obj W).isAddCommGroup ((ofDescent C J O (toDescent C J O F)).val.obj W).isModule
    { toFun := fun x ↦ cartesianUnitAppFun C J O F W.unop x
      map_add' := (cartesianUnitApp_linear C J O F W).1.1
      map_smul' := (cartesianUnitApp_linear C J O F W).1.2 }

/-- The inv comparison on sections, bundled as a linear map. -/
private def cartesianUnitAppInv (F : Cartesian C J O) (W : (totalSite C)ᵒᵖ) :
    (ofDescent C J O (toDescent C J O F)).val.obj W ⟶ (F.obj).val.obj W :=
  @ModuleCat.ofHom _ _ ((ofDescent C J O (toDescent C J O F)).val.obj W) (F.obj.val.obj W)
    ((ofDescent C J O (toDescent C J O F)).val.obj W).isAddCommGroup ((ofDescent C J O (toDescent C J O F)).val.obj W).isModule
    (F.obj.val.obj W).isAddCommGroup (F.obj.val.obj W).isModule
    { toFun := fun x ↦ cartesianUnitAppInvFun C J O F W.unop x
      map_add' := (cartesianUnitApp_linear C J O F W).2.1
      map_smul' := (cartesianUnitApp_linear C J O F W).2.2 }

/-- The comparison maps are natural in the site and are mutually inverse on sections. -/
private theorem cartesianUnitSheafIso_laws (F : Cartesian C J O) :
    (∀ {W Z : (totalSite C)ᵒᵖ} (η : W ⟶ Z),
      (F.obj).val.map η ≫
          (ModuleCat.restrictScalars ((totalRingedSite C J O).structureSheaf.obj.map η).hom).map (cartesianUnitAppHom C J O F Z) =
        cartesianUnitAppHom C J O F W ≫ (ofDescent C J O (toDescent C J O F)).val.map η) ∧
    (∀ {W Z : (totalSite C)ᵒᵖ} (η : W ⟶ Z),
      (ofDescent C J O (toDescent C J O F)).val.map η ≫
          (ModuleCat.restrictScalars ((totalRingedSite C J O).structureSheaf.obj.map η).hom).map (cartesianUnitAppInv C J O F Z) =
        cartesianUnitAppInv C J O F W ≫ (F.obj).val.map η) ∧
    (∀ (W : (totalSite C)ᵒᵖ), cartesianUnitAppHom C J O F W ≫ cartesianUnitAppInv C J O F W = 𝟙 _) ∧
    (∀ (W : (totalSite C)ᵒᵖ), cartesianUnitAppInv C J O F W ≫ cartesianUnitAppHom C J O F W = 𝟙 _) := sorry

/-- The specified section comparisons form an isomorphism of module sheaves. -/
private def cartesianUnitSheafIso (F : Cartesian C J O) :
    F.obj ≅ ofDescent C J O (toDescent C J O F) where
  hom :=
    { val :=
        { app := cartesianUnitAppHom C J O F
          naturality := (cartesianUnitSheafIso_laws C J O F).1 } }
  inv :=
    { val :=
        { app := cartesianUnitAppInv C J O F
          naturality := (cartesianUnitSheafIso_laws C J O F).2.1 } }
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    exact (cartesianUnitSheafIso_laws C J O F).2.2.1 W
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    exact (cartesianUnitSheafIso_laws C J O F).2.2.2 W

/-- The unit isomorphism of the cartesian / face-descent equivalence, at an object `F`. -/
private def cartesianUnitApp (F : Cartesian C J O) :
    F ≅ (ofDescentFunctor C J O).obj ((toDescentFunctor C J O).obj F) :=
  (cartesianProperty C J O).isoMk (cartesianUnitSheafIso C J O F)

/-- The unit components commute with morphisms of cartesian modules. -/
private theorem cartesianUnitIso_naturality {F G : Cartesian C J O} (f : F ⟶ G) :
    f ≫ (cartesianUnitApp C J O G).hom =
      (cartesianUnitApp C J O F).hom ≫
        (toDescentFunctor C J O ⋙ ofDescentFunctor C J O).map f := sorry

/-- The unit natural isomorphism `𝟭 ≅ toDescentFunctor ⋙ ofDescentFunctor`. -/
private def cartesianUnitIso :
    𝟭 (Cartesian C J O) ≅ toDescentFunctor C J O ⋙ ofDescentFunctor C J O :=
  NatIso.ofComponents (fun F ↦ cartesianUnitApp C J O F) (fun f ↦ cartesianUnitIso_naturality C J O f)

/-- Underlying function of `ofDescentComponentZeroIso.hom` at a degree-zero object. -/
private def ofDescentComponentZeroHomFun (D : FaceDescent C J O) (V : C.obj ⦋0⦌)
    (x : ((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj (op V)) :
    ((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj (op V) :=
  ((ofStage C ⦋0⦌).sheafPushforwardContinuousObjObjIso (Type w)
      (totalUnderlying C J O (ofDescent C J O D)) V).hom
    ((modulePullback_underlyingIso C J O ⦋0⦌ (ofDescent C J O D)).hom.hom.app (op V) x)

/-- Underlying function of `ofDescentComponentZeroIso.inv` at a degree-zero object. -/
private def ofDescentComponentZeroInvFun (D : FaceDescent C J O) (V : C.obj ⦋0⦌)
    (x : ((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj
      (op V)) :
    ((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj (op V) :=
  (modulePullback_underlyingIso C J O ⦋0⦌ (ofDescent C J O D)).inv.hom.app (op V)
    (((ofStage C ⦋0⦌).sheafPushforwardContinuousObjObjIso (Type w)
      (totalUnderlying C J O (ofDescent C J O D)) V).inv x)

/-- The forward and inverse comparison functions preserve addition and scalar multiplication. -/
private theorem ofDescentComponentZeroApp_linear (D : FaceDescent C J O) (W : (C.obj ⦋0⦌)ᵒᵖ) :
    ((∀ x y : ((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj W,
      ofDescentComponentZeroHomFun C J O D W.unop (x + y) =
        ofDescentComponentZeroHomFun C J O D W.unop x + ofDescentComponentZeroHomFun C J O D W.unop y) ∧
    (∀ (r : (componentRingedSite C J O ⦋0⦌).structureSheaf.obj.obj W)
      (x : ((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj W),
      ofDescentComponentZeroHomFun C J O D W.unop (r • x) =
        @SMul.smul _ _ (((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj W).isModule.toSMul r
          (ofDescentComponentZeroHomFun C J O D W.unop x))) ∧
    ((∀ x y : ((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj W,
      ofDescentComponentZeroInvFun C J O D W.unop (x + y) =
        ofDescentComponentZeroInvFun C J O D W.unop x + ofDescentComponentZeroInvFun C J O D W.unop y) ∧
    (∀ (r : (componentRingedSite C J O ⦋0⦌).structureSheaf.obj.obj W)
      (x : ((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj W),
      ofDescentComponentZeroInvFun C J O D W.unop (r • x) =
        @SMul.smul _ _ (((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj W).isModule.toSMul r
          (ofDescentComponentZeroInvFun C J O D W.unop x))) := sorry

/-- The hom comparison on sections, bundled as a linear map. -/
private def ofDescentComponentZeroAppHom (D : FaceDescent C J O) (W : (C.obj ⦋0⦌)ᵒᵖ) :
    ((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj W ⟶ ((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj W :=
  @ModuleCat.ofHom _ _ (((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj W) (((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj W)
    (((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj W).isAddCommGroup (((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj W).isModule
    (((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj W).isAddCommGroup (((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj W).isModule
    { toFun := fun x ↦ ofDescentComponentZeroHomFun C J O D W.unop x
      map_add' := (ofDescentComponentZeroApp_linear C J O D W).1.1
      map_smul' := (ofDescentComponentZeroApp_linear C J O D W).1.2 }

/-- The inv comparison on sections, bundled as a linear map. -/
private def ofDescentComponentZeroAppInv (D : FaceDescent C J O) (W : (C.obj ⦋0⦌)ᵒᵖ) :
    ((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj W ⟶ ((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj W :=
  @ModuleCat.ofHom _ _ (((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj W) (((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj W)
    (((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj W).isAddCommGroup (((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj W).isModule
    (((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj W).isAddCommGroup (((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj W).isModule
    { toFun := fun x ↦ ofDescentComponentZeroInvFun C J O D W.unop x
      map_add' := (ofDescentComponentZeroApp_linear C J O D W).2.1
      map_smul' := (ofDescentComponentZeroApp_linear C J O D W).2.2 }

/-- The comparison maps are natural in the site and are mutually inverse on sections. -/
private theorem ofDescentComponentZeroIso_laws (D : FaceDescent C J O) :
    (∀ {W Z : (C.obj ⦋0⦌)ᵒᵖ} (η : W ⟶ Z),
      ((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.map η ≫
          (ModuleCat.restrictScalars ((componentRingedSite C J O ⦋0⦌).structureSheaf.obj.map η).hom).map (ofDescentComponentZeroAppHom C J O D Z) =
        ofDescentComponentZeroAppHom C J O D W ≫ ((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.map η) ∧
    (∀ {W Z : (C.obj ⦋0⦌)ᵒᵖ} (η : W ⟶ Z),
      ((ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module).val.map η ≫
          (ModuleCat.restrictScalars ((componentRingedSite C J O ⦋0⦌).structureSheaf.obj.map η).hom).map (ofDescentComponentZeroAppInv C J O D Z) =
        ofDescentComponentZeroAppInv C J O D W ≫ ((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.map η) ∧
    (∀ (W : (C.obj ⦋0⦌)ᵒᵖ), ofDescentComponentZeroAppHom C J O D W ≫ ofDescentComponentZeroAppInv C J O D W = 𝟙 _) ∧
    (∀ (W : (C.obj ⦋0⦌)ᵒᵖ), ofDescentComponentZeroAppInv C J O D W ≫ ofDescentComponentZeroAppHom C J O D W = 𝟙 _) := sorry

/-- The specified section comparisons form an isomorphism of module sheaves. -/
private def ofDescentComponentZeroIso (D : FaceDescent C J O) :
    (moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D) ≅ (ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module where
  hom :=
    { val :=
        { app := ofDescentComponentZeroAppHom C J O D
          naturality := (ofDescentComponentZeroIso_laws C J O D).1 } }
  inv :=
    { val :=
        { app := ofDescentComponentZeroAppInv C J O D
          naturality := (ofDescentComponentZeroIso_laws C J O D).2.1 } }
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    exact (ofDescentComponentZeroIso_laws C J O D).2.2.1 W
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    exact (ofDescentComponentZeroIso_laws C J O D).2.2.2 W

/-- Identification of `(f_{τ^0_0})^* F` with `F` via `τ^0_0 = id`. -/
private def vertexOpZeroIso (D : FaceDescent C J O) :
    (ringedToposMap C J O (vertexOp ⦋0⦌)).modulePullback.obj D.module ≅ D.module :=
  (recodeModulePullback C J O
      (SimplexCategory.Hom.ext_zero_left (vertexOp ⦋0⦌) (𝟙 ⦋0⦌))).app D.module ≪≫
    (ringedModulePullbackIdIso C J O ⦋0⦌).app D.module

/-- The degree-zero comparison and its inverse respect descent and satisfy the inverse laws. -/
private theorem cartesianCounitApp_laws (D : FaceDescent C J O) :
    let E := (toDescentFunctor C J O).obj ((ofDescentFunctor C J O).obj D)
    let h := (ofDescentComponentZeroIso C J O D).hom ≫ (vertexOpZeroIso C J O D).hom
    let i := (vertexOpZeroIso C J O D).inv ≫ (ofDescentComponentZeroIso C J O D).inv
    ((ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map h ≫ D.iso.hom =
      E.iso.hom ≫
        (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map h) ∧
    ((ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map i ≫ E.iso.hom =
      D.iso.hom ≫
        (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map i) ∧
    (h ≫ i = 𝟙 E.module) ∧ (i ≫ h = 𝟙 D.module) := sorry

/-- The counit compares the reconstructed degree-zero descent pair with the original pair. -/
private def cartesianCounitApp (D : FaceDescent C J O) :
    (toDescentFunctor C J O).obj ((ofDescentFunctor C J O).obj D) ≅ D where
  hom := FaceDescent.homMk
    ((ofDescentComponentZeroIso C J O D).hom ≫ (vertexOpZeroIso C J O D).hom)
    (cartesianCounitApp_laws C J O D).1
  inv := FaceDescent.homMk
    ((vertexOpZeroIso C J O D).inv ≫ (ofDescentComponentZeroIso C J O D).inv)
    (cartesianCounitApp_laws C J O D).2.1
  hom_inv_id := by
    apply InducedWideCategory.Hom.ext
    apply InducedCategory.hom_ext
    exact (cartesianCounitApp_laws C J O D).2.2.1
  inv_hom_id := by
    apply InducedWideCategory.Hom.ext
    apply InducedCategory.hom_ext
    exact (cartesianCounitApp_laws C J O D).2.2.2

/-- The counit components commute with morphisms of descent pairs. -/
private theorem cartesianCounitIso_naturality {D E : FaceDescent C J O} (f : D ⟶ E) :
    (ofDescentFunctor C J O ⋙ toDescentFunctor C J O).map f ≫
        (cartesianCounitApp C J O E).hom =
      (cartesianCounitApp C J O D).hom ≫ f := sorry

/-- The counit natural isomorphism `ofDescentFunctor ⋙ toDescentFunctor ≅ 𝟭`. -/
private def cartesianCounitIso :
    ofDescentFunctor C J O ⋙ toDescentFunctor C J O ≅ 𝟭 (FaceDescent C J O) :=
  NatIso.ofComponents (fun D ↦ cartesianCounitApp C J O D) (fun f ↦ cartesianCounitIso_naturality C J O f)

/-- Cartesian `O`-modules on `C_total` are equivalent to face-descent pairs `(F, α)`. -/
def cartesianEquivalence : Cartesian C J O ≌ FaceDescent C J O :=
  Equivalence.mk (toDescentFunctor C J O) (ofDescentFunctor C J O)
    (cartesianUnitIso C J O) (cartesianCounitIso C J O)

/-- The forward functor of `cartesianEquivalence` extracts the pair `(F_0, α)`. -/
theorem cartesianEquivalence_functor :
    (cartesianEquivalence C J O).functor = toDescentFunctor C J O := rfl

/-- The inverse functor of `cartesianEquivalence` assembles a cartesian `O`-module from a pair
`(F, α)`. -/
theorem cartesianEquivalence_inverse :
    (cartesianEquivalence C J O).inverse = ofDescentFunctor C J O := rfl

end CategoryTheory.SimplicialSites.Module
