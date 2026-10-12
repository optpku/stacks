/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap85.Lemma_85_12_5_Descent

/-!
# Equivalence between cartesian modules and face-descent data

Cartesian `O`-modules on `C_total` are equivalent to pairs `(F, α)` of an `O_0`-module
and an `O_1`-module isomorphism satisfying the `O_2` cocycle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites.Module

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
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

/-- The structure morphism of a cartesian `O`-module is cartesian. -/
theorem cartesian_isCartesian (F : Cartesian C J O) : IsCartesian C J O F.obj :=
  sorry

/-- The isomorphism `f_φ^* F_m ≅ F_n` extracted from a cartesianness proof. -/
def cartesianFaceIso (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    (h : IsCartesian C J O F) {m n : SimplexCategory} (φ : m ⟶ n) :
    (ringedToposMap C J O φ).modulePullback.obj ((moduleComponent C J O m).obj F) ≅
      (moduleComponent C J O n).obj F :=
  @asIso _ _ _ _ (moduleTransition C J O φ F) (h.isIso_transition φ)

/-- The forward map of `cartesianFaceIso` is `moduleTransition`. -/
theorem cartesianFaceIso_hom
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    (h : IsCartesian C J O F) {m n : SimplexCategory} (φ : m ⟶ n) :
    (cartesianFaceIso C J O F h φ).hom = moduleTransition C J O φ F :=
  sorry

/-- Extract the pair `(F_0, α)` from a cartesian `O`-module, with
`α = F(δ 1) ≪≫ F(δ 0).symm`. -/
def toDescent (F : Cartesian C J O) : FaceDescent C J O :=
  FaceDescent.ofIso ((moduleComponent C J O ⦋0⦌).obj F.obj)
    (cartesianFaceIso C J O F.obj F.property (SimplexCategory.δ (1 : Fin 2)) ≪≫
      (cartesianFaceIso C J O F.obj F.property (SimplexCategory.δ (0 : Fin 2))).symm)
    sorry

/-- The `O_0`-module extracted by `toDescent` is the degree-zero component. -/
theorem toDescent_module (F : Cartesian C J O) :
    (toDescent C J O F).module = (moduleComponent C J O ⦋0⦌).obj F.obj :=
  sorry

/-- Ring identification `O_n(obj U) ⟶ O(U)` from `U = ofObj (degree U) (obj U)`. -/
def componentRingEval (U : totalSite C) :
    (componentRingedSite C J O (degree U)).structureSheaf.obj.obj (op (obj U)) ⟶
      (totalRingedSite C J O).structureSheaf.obj.obj (op U) :=
  (totalRingedSite C J O).structureSheaf.obj.map (eqToHom (rfl : U = ofObj C (degree U) (obj U))).op

/-- Evaluation of `(f_{τ^{deg U}_{deg U}})^* F` at `obj U`. -/
def vertexPullbackEval (D : FaceDescent C J O) (U : totalSite C) :
    ModuleCat.{w}
      ((componentRingedSite C J O (degree U)).structureSheaf.obj.obj (op (obj U))) :=
  ((ringedToposMap C J O (Sheaf.vertexOp (degree U))).modulePullback.obj D.module).val.obj
    (op (obj U))

/-- Sections of the reconstructed module over `U`, as an `O(U)`-module. -/
def ofDescentObj (D : FaceDescent C J O) (U : totalSite C) :
    ModuleCat.{w} ((totalRingedSite C J O).structureSheaf.obj.obj (op U)) :=
  (ModuleCat.restrictScalars (componentRingEval C J O U).hom).obj
    (vertexPullbackEval C J O D U)

/-- Direct-image mate of `transitionOf φ D`, as an `O_n`-module map. -/
def transitionOfMate {n m : SimplexCategory} (φ : n ⟶ m) (D : FaceDescent C J O) :
    (ringedToposMap C J O (Sheaf.vertexOp n)).modulePullback.obj D.module ⟶
      (ringedToposMap C J O φ).modulePushforward.obj
        ((ringedToposMap C J O (Sheaf.vertexOp m)).modulePullback.obj D.module) :=
  ((ringedToposMap C J O φ).moduleAdjunction.homEquiv
      ((ringedToposMap C J O (Sheaf.vertexOp n)).modulePullback.obj D.module)
      ((ringedToposMap C J O (Sheaf.vertexOp m)).modulePullback.obj D.module))
    (FaceDescent.transitionOf φ D)

/-- Underlying function of module pushforward evaluation along `u_φ`. -/
def modulePushforwardEvalFun {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (componentRingedSite C J O n).structureSheaf) (U : C.obj m) :
    ((ringedToposMap C J O φ).modulePushforward.obj M).val.obj (op U) →
      M.val.obj (op ((C.map φ).toFunctor.obj U)) :=
  fun x ↦
    ((ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O φ)).hom.app M).hom.app
      (op U) x

/-- Underlying restriction of a reconstructed module along a total-category morphism `(φ, g)`. -/
def ofDescentMapFun (D : FaceDescent C J O) {U V : totalSite C} (η : U ⟶ V)
    (x : vertexPullbackEval C J O D V) : vertexPullbackEval C J O D U :=
  (((ringedToposMap C J O (Sheaf.vertexOp (degree U))).modulePullback.obj D.module).val.map
      (homToPair η).2.op)
    (modulePushforwardEvalFun C J O (homToPair η).1
      ((ringedToposMap C J O (Sheaf.vertexOp (degree U))).modulePullback.obj D.module)
      (obj V)
      ((transitionOfMate C J O (homToPair η).1 D).val.app (op (obj V)) x))

/-- Package an additive map of underlying sections as a morphism in `ModuleCat`. -/
def moduleCatHomOfFun {R : RingCat.{w}} {M N : ModuleCat.{w} R} (f : M → N) : M ⟶ N :=
  @ModuleCat.ofHom R _ M N M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule
    { toFun := f
      map_add' := sorry
      map_smul' := sorry }

/-- Restriction of a reconstructed module along a total-category morphism, as an `O`-linear
map. -/
def ofDescentValMap (D : FaceDescent C J O) {W Z : (totalSite C)ᵒᵖ} (η : W ⟶ Z) :
    ofDescentObj C J O D W.unop ⟶
      (ModuleCat.restrictScalars
        ((totalRingedSite C J O).structureSheaf.obj.map η).hom).obj
        (ofDescentObj C J O D Z.unop) :=
  moduleCatHomOfFun (fun x ↦ ofDescentMapFun C J O D η.unop x)

/-- The assembled presheaf of `O`-modules associated to a pair `(F, α)`: value at `U` is
`(f_{τ^{deg U}_{deg U}})^* F` at `obj U`. -/
def ofDescentPresheaf (D : FaceDescent C J O) :
    PresheafOfModules.{w} (totalRingedSite C J O).structureSheaf.obj where
  obj W := ofDescentObj C J O D W.unop
  map η := ofDescentValMap C J O D η
  map_id := sorry
  map_comp := sorry

/-- Assemble a sheaf of `O`-modules on `C_total` from a face-descent pair. -/
def ofDescent (D : FaceDescent C J O) :
    SheafOfModules.{w} (totalRingedSite C J O).structureSheaf where
  val := ofDescentPresheaf C J O D
  isSheaf := sorry

/-- Sections of `ofDescent D` over `U` are the sections of `(f_{τ^{deg U}_{deg U}})^* F`
over `obj U`, transported along `componentRingEval`. -/
theorem ofDescent_obj_app (D : FaceDescent C J O) (U : totalSite C) :
    (ofDescent C J O D).val.obj (op U) = ofDescentObj C J O D U :=
  sorry

/-- The `O`-module morphism on `C_total` induced by a morphism of face-descent pairs. -/
def ofDescentMap {D E : FaceDescent C J O} (α : FaceDescent.Hom D E) :
    ofDescent C J O D ⟶ ofDescent C J O E where
  val :=
    { app := fun W ↦
        moduleCatHomOfFun fun x ↦
          ((ringedToposMap C J O (Sheaf.vertexOp (degree W.unop))).modulePullback.map
              α.hom).val.app (op (obj W.unop)) x
      naturality := sorry }

/-- The functor sending a cartesian `O`-module to the extracted pair `(F_0, α)`. -/
def toDescentFunctor : Cartesian C J O ⥤ FaceDescent C J O where
  obj F := toDescent C J O F
  map {F G} f := FaceDescent.homMk ((moduleComponent C J O ⦋0⦌).map f.hom) sorry
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- On objects, `toDescentFunctor` is `toDescent`. -/
theorem toDescentFunctor_obj (F : Cartesian C J O) :
    (toDescentFunctor C J O).obj F = toDescent C J O F :=
  sorry

/-- The functor assembling a cartesian `O`-module on `C_total` from a face-descent pair. -/
def ofDescentFunctor : FaceDescent C J O ⥤ Cartesian C J O where
  obj D := ⟨ofDescent C J O D, sorry⟩
  map {D E} α := ObjectProperty.homMk (ofDescentMap C J O α)
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- On objects, the underlying module of `ofDescentFunctor` is `ofDescent`. -/
theorem ofDescentFunctor_obj_obj (D : FaceDescent C J O) :
    ((ofDescentFunctor C J O).obj D).obj = ofDescent C J O D :=
  sorry

/-- Underlying type-valued sheaf of an `O`-module on `C_total`. -/
abbrev totalUnderlying (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    Sheaf (topology C J) (Type w) :=
  (Sheaf.InternalModule.ToInternal.underlying
      (totalRingedSite C J O).structureSheaf).obj F

/-- Evaluation of geometric inverse image along the stage inclusion `g_n`. -/
def moduleInverseImageEval
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    (n : SimplexCategory) (U : C.obj n) :
    ModuleCat.{w}
      (((stageMorphism C J O n).toTopos.ringInverseImage.obj
          (totalRingedSite C J O).structureSheaf).obj.obj (op U)) :=
  (((stageMorphism C J O n).toTopos.moduleInverseImage
      (totalRingedSite C J O).structureSheaf).obj F).val.obj (op U)

/-- The extend/restrict unit of `g_n` at the geometric inverse image of `F`. -/
def extendRestrictUnitApp
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    (n : SimplexCategory) :
    ((stageMorphism C J O n).toTopos.moduleInverseImage
        (totalRingedSite C J O).structureSheaf).obj F ⟶
      (SheafOfModules.restrictScalars.{w} (stageMorphism C J O n).structureMap).obj
        ((moduleComponent C J O n).obj F) :=
  (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
      (stageMorphism C J O n).structureMap).unit.app
    (((stageMorphism C J O n).toTopos.moduleInverseImage
        (totalRingedSite C J O).structureSheaf).obj F)

/-- `extendRestrictUnitApp` is the unit of the extend/restrict adjunction along
the structure map of `g_n`. -/
theorem extendRestrictUnitApp_eq
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    (n : SimplexCategory) :
    extendRestrictUnitApp C J O F n =
      (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
          (stageMorphism C J O n).structureMap).unit.app
        (((stageMorphism C J O n).toTopos.moduleInverseImage
            (totalRingedSite C J O).structureSheaf).obj F) :=
  sorry

/-- The extend/restrict unit along the identity structure map of `g_n` is an
isomorphism: `stageIdentityComparison` is `𝟙`. -/
instance isIso_extendRestrictUnitApp
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    (n : SimplexCategory) :
    IsIso (extendRestrictUnitApp C J O F n) :=
  sorry

/-- Inverse of the extend/restrict unit of `g_n`, as an isomorphism of sheaves of
modules. Isomorphism laws remain deferred. -/
def extendRestrictUnitIso
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    (n : SimplexCategory) :
    ((stageMorphism C J O n).toTopos.moduleInverseImage
        (totalRingedSite C J O).structureSheaf).obj F ≅
      (SheafOfModules.restrictScalars.{w} (stageMorphism C J O n).structureMap).obj
        ((moduleComponent C J O n).obj F) :=
  asIso (extendRestrictUnitApp C J O F n)

/-- The forward map of `extendRestrictUnitIso` is the extend/restrict unit. -/
theorem extendRestrictUnitIso_hom
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    (n : SimplexCategory) :
    (extendRestrictUnitIso C J O F n).hom = extendRestrictUnitApp C J O F n :=
  sorry

/-- Scalar-extension unit from geometric inverse image to stage restriction, evaluated at `U`. -/
def extendUnitEvalFun
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    (n : SimplexCategory) (U : C.obj n) (x : moduleInverseImageEval C J O F n U) :
    ((SheafOfModules.restrictScalars.{w} (stageMorphism C J O n).structureMap).obj
      ((moduleComponent C J O n).obj F)).val.obj (op U) :=
  (extendRestrictUnitApp C J O F n).val.app (op U) x

/-- Inverse of `extendUnitEvalFun`, as the underlying component of
`(extendRestrictUnitIso C J O F n).inv`. -/
def extendUnitInvEvalFun
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    (n : SimplexCategory) (U : C.obj n)
    (x : ((SheafOfModules.restrictScalars.{w} (stageMorphism C J O n).structureMap).obj
      ((moduleComponent C J O n).obj F)).val.obj (op U)) :
    moduleInverseImageEval C J O F n U :=
  (extendRestrictUnitIso C J O F n).inv.val.app (op U) x

/-- `extendUnitInvEvalFun` is the section-level inverse of the extend/restrict unit. -/
theorem extendUnitInvEvalFun_eq
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    (n : SimplexCategory) (U : C.obj n)
    (x : ((SheafOfModules.restrictScalars.{w} (stageMorphism C J O n).structureMap).obj
      ((moduleComponent C J O n).obj F)).val.obj (op U)) :
    extendUnitInvEvalFun C J O F n U x =
      (extendRestrictUnitIso C J O F n).inv.val.app (op U) x :=
  sorry

/-- Component of the unit isomorphism on underlying sections. -/
def cartesianUnitAppFun (F : Cartesian C J O) (U : totalSite C)
    (x : F.obj.val.obj (op U)) : vertexPullbackEval C J O (toDescent C J O F) U :=
  (cartesianFaceIso C J O F.obj F.property (Sheaf.vertexOp (degree U))).inv.val.app
      (op (obj U))
    (extendUnitEvalFun C J O F.obj (degree U) (obj U)
      ((moduleInverseImage_underlyingIso C J O F.obj (degree U)).inv.hom.app (op (obj U))
        ((component_obj C J (Type w) (degree U) (totalUnderlying C J O F.obj) (obj U)).inv
          (F.obj.val.map (eqToHom (rfl : U = ofObj C (degree U) (obj U))).op x))))

/-- Component of the inverse unit isomorphism on underlying sections. -/
def cartesianUnitAppInvFun (F : Cartesian C J O) (U : totalSite C)
    (x : vertexPullbackEval C J O (toDescent C J O F) U) : F.obj.val.obj (op U) :=
  F.obj.val.map (eqToHom (rfl : U = ofObj C (degree U) (obj U)).symm).op
    ((component_obj C J (Type w) (degree U) (totalUnderlying C J O F.obj) (obj U)).hom
      ((moduleInverseImage_underlyingIso C J O F.obj (degree U)).hom.hom.app (op (obj U))
        (extendUnitInvEvalFun C J O F.obj (degree U) (obj U)
          ((cartesianFaceIso C J O F.obj F.property (Sheaf.vertexOp (degree U))).hom.val.app
            (op (obj U)) x))))

/-- The unit isomorphism on underlying sheaves of the cartesian / face-descent equivalence. -/
def cartesianUnitSheafIso (F : Cartesian C J O) :
    F.obj ≅ ofDescent C J O (toDescent C J O F) where
  hom :=
    { val :=
        { app := fun W ↦
            moduleCatHomOfFun fun x ↦ cartesianUnitAppFun C J O F W.unop x
          naturality := sorry } }
  inv :=
    { val :=
        { app := fun W ↦
            moduleCatHomOfFun fun x ↦ cartesianUnitAppInvFun C J O F W.unop x
          naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The unit isomorphism of the cartesian / face-descent equivalence, at an object `F`. -/
def cartesianUnitApp (F : Cartesian C J O) :
    F ≅ (ofDescentFunctor C J O).obj ((toDescentFunctor C J O).obj F) :=
  (cartesianProperty C J O).isoMk (cartesianUnitSheafIso C J O F)

/-- The unit natural isomorphism `𝟭 ≅ toDescentFunctor ⋙ ofDescentFunctor`. -/
def cartesianUnitIso :
    𝟭 (Cartesian C J O) ≅ toDescentFunctor C J O ⋙ ofDescentFunctor C J O :=
  NatIso.ofComponents (fun F ↦ cartesianUnitApp C J O F) sorry

/-- Underlying function of `ofDescentComponentZeroIso.hom` at a degree-zero object. -/
def ofDescentComponentZeroHomFun (D : FaceDescent C J O) (V : C.obj ⦋0⦌)
    (x : ((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj (op V)) :
    ((ringedToposMap C J O (Sheaf.vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj (op V) :=
  (component_obj C J (Type w) ⦋0⦌ (totalUnderlying C J O (ofDescent C J O D)) V).hom
    ((moduleInverseImage_underlyingIso C J O (ofDescent C J O D) ⦋0⦌).hom.hom.app (op V)
      (extendUnitInvEvalFun C J O (ofDescent C J O D) ⦋0⦌ V x))

/-- Underlying function of `ofDescentComponentZeroIso.inv` at a degree-zero object. -/
def ofDescentComponentZeroInvFun (D : FaceDescent C J O) (V : C.obj ⦋0⦌)
    (x : ((ringedToposMap C J O (Sheaf.vertexOp ⦋0⦌)).modulePullback.obj D.module).val.obj
      (op V)) :
    ((moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D)).val.obj (op V) :=
  extendUnitEvalFun C J O (ofDescent C J O D) ⦋0⦌ V
    ((moduleInverseImage_underlyingIso C J O (ofDescent C J O D) ⦋0⦌).inv.hom.app (op V)
      ((component_obj C J (Type w) ⦋0⦌ (totalUnderlying C J O (ofDescent C J O D)) V).inv x))

/-- Comparison of the degree-zero restriction of `ofDescent D` with `(f_{τ^0_0})^* F`. -/
def ofDescentComponentZeroIso (D : FaceDescent C J O) :
    (moduleComponent C J O ⦋0⦌).obj (ofDescent C J O D) ≅
      (ringedToposMap C J O (Sheaf.vertexOp ⦋0⦌)).modulePullback.obj D.module where
  hom :=
    { val :=
        { app := fun V ↦
            moduleCatHomOfFun fun x ↦ ofDescentComponentZeroHomFun C J O D V.unop x
          naturality := sorry } }
  inv :=
    { val :=
        { app := fun V ↦
            moduleCatHomOfFun fun x ↦ ofDescentComponentZeroInvFun C J O D V.unop x
          naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identification of `(f_{τ^0_0})^* F` with `F` via `τ^0_0 = id`. -/
def vertexOpZeroIso (D : FaceDescent C J O) :
    (ringedToposMap C J O (Sheaf.vertexOp ⦋0⦌)).modulePullback.obj D.module ≅ D.module :=
  (recodeModulePullback C J O
      (SimplexCategory.Hom.ext_zero_left (Sheaf.vertexOp ⦋0⦌) (𝟙 ⦋0⦌))).app D.module ≪≫
    (ringedModulePullbackIdIso C J O ⦋0⦌).app D.module

/-- The counit isomorphism of the cartesian / face-descent equivalence, at a pair `D`. -/
def cartesianCounitApp (D : FaceDescent C J O) :
    (toDescentFunctor C J O).obj ((ofDescentFunctor C J O).obj D) ≅ D where
  hom :=
    FaceDescent.homMk
      ((ofDescentComponentZeroIso C J O D).hom ≫ (vertexOpZeroIso C J O D).hom) sorry
  inv :=
    FaceDescent.homMk
      ((vertexOpZeroIso C J O D).inv ≫ (ofDescentComponentZeroIso C J O D).inv) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The counit natural isomorphism `ofDescentFunctor ⋙ toDescentFunctor ≅ 𝟭`. -/
def cartesianCounitIso :
    ofDescentFunctor C J O ⋙ toDescentFunctor C J O ≅ 𝟭 (FaceDescent C J O) :=
  NatIso.ofComponents (fun D ↦ cartesianCounitApp C J O D) sorry

/-- Cartesian `O`-modules on `C_total` are equivalent to face-descent pairs `(F, α)`. -/
def cartesianEquivalence : Cartesian C J O ≌ FaceDescent C J O :=
  Equivalence.mk (toDescentFunctor C J O) (ofDescentFunctor C J O)
    (cartesianUnitIso C J O) (cartesianCounitIso C J O)

/-- The forward functor of `cartesianEquivalence` extracts the pair `(F_0, α)`. -/
theorem cartesianEquivalence_functor :
    (cartesianEquivalence C J O).functor = toDescentFunctor C J O :=
  sorry

/-- The inverse functor of `cartesianEquivalence` assembles a cartesian `O`-module from a pair
`(F, α)`. -/
theorem cartesianEquivalence_inverse :
    (cartesianEquivalence C J O).inverse = ofDescentFunctor C J O :=
  sorry

end CategoryTheory.SimplicialSites.Module
