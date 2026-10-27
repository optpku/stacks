/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.Integer
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.ProjectionFormula
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

-- Local declaration justification (metaprogramming implementation): Exposed constructors
-- require private proof laws to remain accessible under Lean module visibility checks.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology.Point
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale.FiniteSupport
open scoped BigOperators AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.WeightingTrace

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- The image of the geometric point of a fibre lift is the base geometric point. -/
theorem fiberPoint_map_eq (ybar : GeometricPoint Y) (x : GeometricPoint.Fiber f ybar) :
    x.point.map f = ybar :=
  congrArg (fun h : Spec (.of ybar.K) ⟶ Y ↦
      ({ toFieldValuedPoint := FieldValuedPoint.of ybar.K h
         isAlgClosed := ybar.isAlgClosed } : GeometricPoint Y))
    x.fac

/-- Inverse-image identification of abelian étale stalks
`(f⁻¹ F)_x̄ ≅ F_ȳ` along `Fiber.fac`. -/
def pullbackStalkIso (ybar : GeometricPoint Y) (x : GeometricPoint.Fiber f ybar)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint x.point).sheafFiber.obj
        ((etaleAbelianSheafPullback f).obj F) ≅
      (toSmallEtalePoint ybar).sheafFiber.obj F :=
  (pullbackSheafFiberIso f x.point F).symm ≪≫
    eqToIso
      (congrArg (fun s : GeometricPoint Y ↦
          (toSmallEtalePoint s).sheafFiber.obj F)
        (fiberPoint_map_eq f ybar x))

/-- Weighted sum of abelian stalks: the coproduct of copies of `F_ȳ` maps to
`F_ȳ` by `zsmul` with `w(x̄.image)` on the summand indexed by `x̄`. -/
def stalkDesc (w : X → ℤ) (ybar : GeometricPoint Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (∐ fun _ : GeometricPoint.Fiber f ybar ↦ (toSmallEtalePoint ybar).sheafFiber.obj F) ⟶
      (toSmallEtalePoint ybar).sheafFiber.obj F :=
  Sigma.desc fun x : GeometricPoint.Fiber f ybar ↦
    w x.point.image • 𝟙 ((toSmallEtalePoint ybar).sheafFiber.obj F)

/-- On the summand indexed by `x`, `stalkDesc` is multiplication by
`w(x.image)`. -/
theorem stalkDesc_app (w : X → ℤ) (ybar : GeometricPoint Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (x : GeometricPoint.Fiber f ybar) :
    Sigma.ι (fun _ : GeometricPoint.Fiber f ybar ↦
        (toSmallEtalePoint ybar).sheafFiber.obj F) x ≫
      stalkDesc f w ybar F =
      w x.point.image •
        𝟙 ((toSmallEtalePoint ybar).sheafFiber.obj F) :=
  sorry

/-- Coproduct of the pullback-stalk identifications
`(f⁻¹ F)_x̄ ≅ F_ȳ`. -/
def pullbackStalkCoproductIso (ybar : GeometricPoint Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianStalkCoproduct f ybar).obj ((etaleAbelianSheafPullback f).obj F) ≅
      ∐ fun _ : GeometricPoint.Fiber f ybar ↦ (toSmallEtalePoint ybar).sheafFiber.obj F :=
  Sigma.mapIso fun x : GeometricPoint.Fiber f ybar ↦ pullbackStalkIso f ybar x F

/-- Coefficient functor sending an abelian group to the associated
`ULift ℤ`-module. -/
def addCommGrpToModule :
    AddCommGrpCat.{u} ⥤ ModuleCat.{u} (ULift.{u} ℤ) :=
  (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom

/-- The coefficient counit preserves zero. -/
private theorem addCommGrpToModuleCounitApp_map_zero (A : AddCommGrpCat.{u}) :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.counitIso.hom.app
        A).hom (0 : (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}).obj
      (addCommGrpToModule.obj A)) = 0 := sorry

/-- The coefficient counit preserves addition. -/
private theorem addCommGrpToModuleCounitApp_map_add (A : AddCommGrpCat.{u})
    (x y : (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}).obj
      (addCommGrpToModule.obj A)) :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.counitIso.hom.app
        A).hom (x + y) = ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.counitIso.hom.app
        A).hom x + ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.counitIso.hom.app
        A).hom y := sorry

/-- Component of the coefficient counit at an abelian group. -/
def addCommGrpToModuleCounitApp (A : AddCommGrpCat.{u}) :
    (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}).obj
      (addCommGrpToModule.obj A) ⟶ A :=
  AddCommGrpCat.ofHom
    { toFun := fun x ↦
        ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.counitIso.hom.app
            A).hom
          (x :
            (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).obj
              ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv.obj A))
      map_zero' := addCommGrpToModuleCounitApp_map_zero A
      map_add' := addCommGrpToModuleCounitApp_map_add A }

/-- Composition with `addCommGrpToModule` preserves étale sheaves. -/
public instance (priority := high) addCommGrpToModule_hasSheafCompose (S : Scheme.{u}) :
    S.smallEtaleTopology.HasSheafCompose addCommGrpToModule :=
  sorry

/-- Composition with `forget₂ (ModuleCat (ULift ℤ))` preserves étale sheaves. -/
public instance (priority := high) forget₂_hasSheafCompose (S : Scheme.{u}) :
    S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}) :=
  sorry

/-- Étale sites have sheafification of `ULift ℤ`-modules. -/
public instance moduleSheaf_hasSheafify (S : Scheme.{u}) :
    HasSheafify S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)) :=
  sorry

/-- The sheafification class `W` is monoidal for étale sheaves of `ULift ℤ`-modules. -/
public instance moduleSheaf_isMonoidal_W (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u} (ULift.{u} ℤ))).IsMonoidal :=
  sorry

/-- `addCommGrpToModule` preserves étale sheafification. -/
public instance addCommGrpToModule_preservesSheafification (S : Scheme.{u}) :
    S.smallEtaleTopology.PreservesSheafification addCommGrpToModule :=
  sorry

/-- `forget₂ (ModuleCat (ULift ℤ))` preserves étale sheafification. -/
public instance forget₂_preservesSheafification (S : Scheme.{u}) :
    S.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}) :=
  sorry

/-- Left Kan extensions of module-valued presheaves along small-étale pullback. -/
public instance pullback_hasLeftKanExtension_module
    (P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} (ULift.{u} ℤ)) :
    (smallEtalePullback f).op.HasLeftKanExtension P :=
  sorry

/-- Left Kan extensions of abelian presheaves along small-étale pullback. -/
public instance pullback_hasLeftKanExtension_abelian
    (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (smallEtalePullback f).op.HasLeftKanExtension P :=
  sorry

/-- `forget₂ (ModuleCat (ULift ℤ))` preserves left Kan extensions along
small-étale pullback. -/
public instance forget₂_preservesLeftKanExtensions :
    (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (smallEtalePullback f).op :=
  sorry

/-- Lift an abelian étale sheaf to a sheaf of `ULift ℤ`-modules. -/
def abelianToModule {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose addCommGrpToModule]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)) :=
  (sheafCompose S.smallEtaleTopology addCommGrpToModule).obj F

/-- The constant integer sheaf, viewed as a sheaf of `ULift ℤ`-modules. -/
def constantIntegerModule (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [S.smallEtaleTopology.HasSheafCompose addCommGrpToModule] :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)) :=
  abelianToModule (constantIntegerSheaf S.smallEtaleTopology)

/-- Forgetting `ULift ℤ`-module coefficients on sections, as a morphism of
abelian étale sheaves. -/
def forgetAbelianHom {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose addCommGrpToModule]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleModuleForget (ULift.{u} ℤ) (abelianToModule F) ⟶ F :=
  ObjectProperty.homMk
    { app := fun U ↦ addCommGrpToModuleCounitApp (F.obj.obj U)
      naturality := sorry }

/-- The sectionwise forgetful comparison is an isomorphism. -/
instance forgetAbelianHom_isIso {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose addCommGrpToModule]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (forgetAbelianHom F) :=
  sorry

/-- Forgetting `ULift ℤ`-module coefficients recovers the original abelian
étale sheaf. -/
def forgetAbelianIso {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose addCommGrpToModule]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleModuleForget (ULift.{u} ℤ) (abelianToModule F) ≅ F :=
  asIso (forgetAbelianHom F)

/-- An additive morphism of integer-module sheaves preserves scalar multiplication. -/
private theorem liftModuleSheafHom_map_smul {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))}
    (α : etaleModuleForget (ULift.{u} ℤ) F ⟶ etaleModuleForget (ULift.{u} ℤ) G)
    (U : S.Etaleᵒᵖ) (r : ULift.{u} ℤ) (x : F.obj.obj U) :
    (α.hom.app U).hom (((F.obj.obj U).smul r).hom x) =
      ((G.obj.obj U).smul r).hom ((α.hom.app U).hom x) := sorry

/-- The module-linear component of an additive morphism of integer-module sheaves. -/
private def liftModuleSheafHomApp {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))}
    (α : etaleModuleForget (ULift.{u} ℤ) F ⟶ etaleModuleForget (ULift.{u} ℤ) G) (U : S.Etaleᵒᵖ) :
    F.obj.obj U ⟶ G.obj.obj U :=
  ModuleCat.ofHom
    { toAddHom := (α.hom.app U).hom.toAddHom
      map_smul' := fun r x ↦ liftModuleSheafHom_map_smul α U r x }

/-- The module-linear components commute with restriction. -/
private theorem liftModuleSheafHom_naturality {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))}
    (α : etaleModuleForget (ULift.{u} ℤ) F ⟶ etaleModuleForget (ULift.{u} ℤ) G)
    {U V : S.Etaleᵒᵖ} (g : U ⟶ V) :
    F.obj.map g ≫ liftModuleSheafHomApp α V =
      liftModuleSheafHomApp α U ≫ G.obj.map g := sorry

/-- Lift an additive sheaf morphism to integer-module sheaves using its section maps. -/
def liftModuleSheafHom {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))}
    (α : etaleModuleForget (ULift.{u} ℤ) F ⟶ etaleModuleForget (ULift.{u} ℤ) G) : F ⟶ G :=
  ObjectProperty.homMk
    { app := liftModuleSheafHomApp α
      naturality := fun {_ _} g ↦ liftModuleSheafHom_naturality α g }

/-- The lift recovers the original abelian sheaf morphism after forgetting
coefficients. -/
theorem etaleModuleForget_map_liftModuleSheafHom {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))}
    (α : etaleModuleForget (ULift.{u} ℤ) F ⟶
      etaleModuleForget (ULift.{u} ℤ) G) :
    (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})).map
        (liftModuleSheafHom α) = α :=
  sorry

/-- Integer coefficient object as a `ULift ℤ`-module. -/
def integerModuleCoeff : ModuleCat.{u} (ULift.{u} ℤ) :=
  addCommGrpToModule.obj integerCoeff

/-- Comparison of the module lift of `underline ℤ` with the constant sheaf of
the coefficient module. -/
def constantIntegerModuleIso
    (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))]
    [S.smallEtaleTopology.HasSheafCompose addCommGrpToModule]
    [S.smallEtaleTopology.PreservesSheafification addCommGrpToModule] :
    constantIntegerModule S ≅
      (constantSheaf S.smallEtaleTopology
          (ModuleCat.{u} (ULift.{u} ℤ))).obj integerModuleCoeff :=
  (constantCommuteCompose S.smallEtaleTopology
      addCommGrpToModule).app integerCoeff

/-- The coefficient counit at `integerCoeff` is an isomorphism of abelian
groups. -/
instance addCommGrpToModuleCounitApp_integerCoeff_isIso :
    IsIso (addCommGrpToModuleCounitApp integerCoeff) :=
  sorry

/-- The coefficient comparison to the integer module unit preserves addition. -/
private theorem integerModuleCoeffToUnit_map_add (x y : integerModuleCoeff) :
    (addCommGrpToModuleCounitApp integerCoeff).hom (x + y) =
      (addCommGrpToModuleCounitApp integerCoeff).hom x +
        (addCommGrpToModuleCounitApp integerCoeff).hom y := sorry

/-- The coefficient comparison to the integer module unit preserves scalars. -/
private theorem integerModuleCoeffToUnit_map_smul (r : ULift.{u} ℤ)
    (x : integerModuleCoeff.{u}) :
    (addCommGrpToModuleCounitApp integerCoeff).hom
        (((integerModuleCoeff.{u}).smul r).hom x) =
      (((𝟙_ (ModuleCat.{u} (ULift.{u} ℤ))).smul r).hom
        ((addCommGrpToModuleCounitApp integerCoeff).hom x)) := sorry

/-- The inverse coefficient comparison preserves addition. -/
private theorem integerModuleCoeffFromUnit_map_add (x y : ULift.{u} ℤ) :
    ((asIso (addCommGrpToModuleCounitApp integerCoeff)).inv).hom (x + y) =
      ((asIso (addCommGrpToModuleCounitApp integerCoeff)).inv).hom x +
        ((asIso (addCommGrpToModuleCounitApp integerCoeff)).inv).hom y := sorry

/-- The inverse coefficient comparison preserves scalars. -/
private theorem integerModuleCoeffFromUnit_map_smul (r x : ULift.{u} ℤ) :
    ((asIso (addCommGrpToModuleCounitApp integerCoeff)).inv).hom
        (((𝟙_ (ModuleCat.{u} (ULift.{u} ℤ))).smul r).hom x) =
      ((integerModuleCoeff.{u}).smul r).hom
        (((asIso (addCommGrpToModuleCounitApp integerCoeff)).inv).hom x) := sorry

/-- The forward linear comparison from the coefficient module to the tensor unit. -/
private def integerModuleCoeffToUnit :
    integerModuleCoeff ⟶ 𝟙_ (ModuleCat.{u} (ULift.{u} ℤ)) :=
  ModuleCat.ofHom
    { toFun := fun x ↦ (addCommGrpToModuleCounitApp integerCoeff).hom x
      map_add' := integerModuleCoeffToUnit_map_add
      map_smul' := fun r x ↦ integerModuleCoeffToUnit_map_smul r x }

/-- The inverse linear comparison from the tensor unit to the coefficient module. -/
private def integerModuleCoeffFromUnit :
    𝟙_ (ModuleCat.{u} (ULift.{u} ℤ)) ⟶ integerModuleCoeff :=
  ModuleCat.ofHom
    { toFun := fun x ↦ ((asIso (addCommGrpToModuleCounitApp integerCoeff)).inv).hom x
      map_add' := integerModuleCoeffFromUnit_map_add
      map_smul' := fun r x ↦ integerModuleCoeffFromUnit_map_smul r x }

/-- Forward coefficient comparison followed by inverse is the identity. -/
private theorem integerModuleCoeffIsoTensorUnit_hom_inv_id :
    integerModuleCoeffToUnit ≫ integerModuleCoeffFromUnit = 𝟙 integerModuleCoeff := sorry

/-- Inverse coefficient comparison followed by forward is the identity. -/
private theorem integerModuleCoeffIsoTensorUnit_inv_hom_id :
    integerModuleCoeffFromUnit ≫ integerModuleCoeffToUnit =
      𝟙 (𝟙_ (ModuleCat.{u} (ULift.{u} ℤ))) := sorry

/-- The integer coefficient module is isomorphic to the module tensor unit. -/
def integerModuleCoeffIsoTensorUnit :
    integerModuleCoeff ≅ 𝟙_ (ModuleCat.{u} (ULift.{u} ℤ)) where
  hom := integerModuleCoeffToUnit
  inv := integerModuleCoeffFromUnit
  hom_inv_id := integerModuleCoeffIsoTensorUnit_hom_inv_id
  inv_hom_id := integerModuleCoeffIsoTensorUnit_inv_hom_id

/-- The constant module unit is the unit of the canonical sheafified tensor.
It is induced by monoidal sheafification. -/
def moduleSheafTensorUnitIso (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))] :
    (constantSheaf S.smallEtaleTopology
          (ModuleCat.{u} (ULift.{u} ℤ))).obj
        (𝟙_ (ModuleCat.{u} (ULift.{u} ℤ))) ≅
      𝟙_ (Sheaf S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) :=
  (Functor.Monoidal.εIso
    (presheafToSheaf S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))).symm

/-- The module lift of `underline ℤ` is isomorphic to the sheaf tensor unit. -/
def constantIntegerModuleTensorUnitIso (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))]
    [S.smallEtaleTopology.HasSheafCompose addCommGrpToModule]
    [S.smallEtaleTopology.PreservesSheafification addCommGrpToModule] :
    constantIntegerModule S ≅
      𝟙_ (Sheaf S.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) :=
  constantIntegerModuleIso S ≪≫
    (constantSheaf S.smallEtaleTopology
        (ModuleCat.{u} (ULift.{u} ℤ))).mapIso
      integerModuleCoeffIsoTensorUnit ≪≫
    moduleSheafTensorUnitIso S

/-- The integer trace as a morphism of sheaves of `ULift ℤ`-modules. -/
def integerTraceModule {w : X → ℤ} (hw : f.IsWeighting w) :
    (lowerShriekModule f (ULift.{u} ℤ)).obj
        (constantIntegerModule X) ⟶
      constantIntegerModule Y :=
  liftModuleSheafHom
    ((lowerShriekModule_forget f (ULift.{u} ℤ)
          (constantIntegerModule X)).hom ≫
      (lowerShriek f).map (forgetAbelianIso
          (constantIntegerSheaf X.smallEtaleTopology)).hom ≫
      integerTrace f hw ≫
      (forgetAbelianIso (constantIntegerSheaf Y.smallEtaleTopology)).inv)

/-- The integer module trace forgets to the abelian integer trace after the
compact-support and coefficient comparisons. -/
theorem integerTraceModule_forget {w : X → ℤ}
    (hw : f.IsWeighting w) :
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})).map
        (integerTraceModule f hw) =
      (lowerShriekModule_forget f (ULift.{u} ℤ)
          (constantIntegerModule X)).hom ≫
        (lowerShriek f).map (forgetAbelianIso
            (constantIntegerSheaf X.smallEtaleTopology)).hom ≫
        integerTrace f hw ≫
        (forgetAbelianIso (constantIntegerSheaf Y.smallEtaleTopology)).inv :=
  sorry

/-- The module-level trace on `f_! f⁻¹ F`, obtained as the image of
`Tr_ℤ ⊗ 𝟙` under the inverse of the projection comparison `can` and the
identifications `underline ℤ ⊗ f⁻¹ F ≅ f⁻¹ F` and `underline ℤ ⊗ F ≅ F`. -/
def traceModule {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekModule f (ULift.{u} ℤ)).obj
        (((smallEtalePullback f).sheafPullback
            (ModuleCat.{u} (ULift.{u} ℤ))
            Y.smallEtaleTopology X.smallEtaleTopology).obj
          (abelianToModule F)) ⟶
      abelianToModule F :=
  (lowerShriekModule f (ULift.{u} ℤ)).map
      ((λ_ (((smallEtalePullback f).sheafPullback
            (ModuleCat.{u} (ULift.{u} ℤ))
            Y.smallEtaleTopology X.smallEtaleTopology).obj
          (abelianToModule F))).inv ≫
        ((constantIntegerModuleTensorUnitIso X).inv ▷
          ((smallEtalePullback f).sheafPullback
              (ModuleCat.{u} (ULift.{u} ℤ))
              Y.smallEtaleTopology X.smallEtaleTopology).obj
            (abelianToModule F))) ≫
    (lowerShriekProjectionIso f (ULift.{u} ℤ)
        (constantIntegerModule X) (abelianToModule F)).inv ≫
    (integerTraceModule f hw ▷ abelianToModule F) ≫
    ((constantIntegerModuleTensorUnitIso Y).hom ▷
      abelianToModule F) ≫
    (λ_ (abelianToModule F)).hom

/-- Comparison of the forgotten module compact-support image of `f⁻¹ F` with
the abelian compact-support image. -/
def lowerShriekPullbackForgetIso
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleModuleForget (ULift.{u} ℤ)
        ((lowerShriekModule f (ULift.{u} ℤ)).obj
          (((smallEtalePullback f).sheafPullback
              (ModuleCat.{u} (ULift.{u} ℤ))
              Y.smallEtaleTopology X.smallEtaleTopology).obj
            (abelianToModule F))) ≅
      (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) :=
  lowerShriekModule_forget f (ULift.{u} ℤ)
      (((smallEtalePullback f).sheafPullback
          (ModuleCat.{u} (ULift.{u} ℤ))
          Y.smallEtaleTopology X.smallEtaleTopology).obj
        (abelianToModule F)) ≪≫
    (lowerShriek f).mapIso
      ((Functor.sheafPullback.compSheafComposeIso (smallEtalePullback f)
            (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})
            Y.smallEtaleTopology X.smallEtaleTopology).app
          (abelianToModule F) ≪≫
        (etaleAbelianSheafPullback f).mapIso (forgetAbelianIso F))

end AlgebraicGeometry.Scheme.Etale.WeightingTrace

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- The trace of a weighting on an abelian étale sheaf, obtained from the integer trace
by the projection formula and coefficient transport. -/
def weightingTrace {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) ⟶ F :=
  (WeightingTrace.lowerShriekPullbackForgetIso f F).inv ≫
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})).map
        (WeightingTrace.traceModule f hw F) ≫
    (WeightingTrace.forgetAbelianIso F).hom

/-- The prescribed stalk behaviour of `Tr_{f, w, F}`: after the identifications
`(f_! f⁻¹ F)_ȳ ≅ ⊕_{f(x̄)=ȳ} (f⁻¹ F)_x̄ ≅ ⊕_{f(x̄)=ȳ} F_ȳ`, the trace is the
weighted sum `⊕ w(x̄)`. -/
theorem weightingTrace_stalk {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (ybar : GeometricPoint Y) :
    (toSmallEtalePoint ybar).sheafFiber.map (weightingTrace f hw F) =
      (lowerShriekStalkIso f ybar).hom.app ((etaleAbelianSheafPullback f).obj F) ≫
        (WeightingTrace.pullbackStalkCoproductIso f ybar F).hom ≫
          WeightingTrace.stalkDesc f w ybar F :=
  sorry

/-- Uniqueness of the weighting trace: a morphism `φ : f_! f⁻¹ F ⟶ F` agreeing
with the prescribed weighted sum on every geometric stalk equals
`weightingTrace`. -/
theorem weightingTrace_unique {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (φ : (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) ⟶ F)
    (hφ : ∀ ybar : GeometricPoint Y,
      (toSmallEtalePoint ybar).sheafFiber.map φ =
        (lowerShriekStalkIso f ybar).hom.app ((etaleAbelianSheafPullback f).obj F) ≫
          (WeightingTrace.pullbackStalkCoproductIso f ybar F).hom ≫
            WeightingTrace.stalkDesc f w ybar F) :
    φ = weightingTrace f hw F :=
  sorry

/-- Every abelian étale sheaf admits a unique trace with the weighted geometric-stalk formula. -/
theorem weightingTrace_existsUnique {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ∃! φ : (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) ⟶ F,
      ∀ ybar : GeometricPoint Y,
        (toSmallEtalePoint ybar).sheafFiber.map φ =
          (lowerShriekStalkIso f ybar).hom.app ((etaleAbelianSheafPullback f).obj F) ≫
            (WeightingTrace.pullbackStalkCoproductIso f ybar F).hom ≫
              WeightingTrace.stalkDesc f w ybar F := sorry

end AlgebraicGeometry.Scheme.Etale

end
