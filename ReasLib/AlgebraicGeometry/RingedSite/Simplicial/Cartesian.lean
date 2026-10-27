/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.Cartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Operators
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Left

/-!
# Cartesian modules on a simplicial ringed site

Restriction comparisons for module sheaves and their unbounded derived categories.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor RingedSite ComplexShape
open RingedSite.Hom (ModuleDerived)

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram C J]
include instMorphismDiagram instWeakSheafify instLeftKan
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

/-- Restriction of an `O`-module on `C_total` to the degree-`n` site, i.e. `F_n = g_n^* F`. -/
def moduleComponent (n : SimplexCategory) :
    SheafOfModules.{w} (totalRingedSite C J O).structureSheaf ⥤
      SheafOfModules.{w} (componentRingedSite C J O n).structureSheaf :=
  (stageMorphism C J O n).modulePullback

/-- `moduleComponent n` is module pullback along the stage inclusion `g_n`. -/
theorem moduleComponent_eq (n : SimplexCategory) :
    moduleComponent C J O n = (stageMorphism C J O n).modulePullback :=
  rfl

section

variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]

/-- Restriction of an object of `D(O)` to the degree-`n` site, i.e. `K_n = Lg_n^* K`. -/
def moduleDerivedComponent (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (totalRingedSite C J O) ⥤
      Hom.ModuleDerived.{w} (componentRingedSite C J O n) :=
  (stageMorphism C J O n).modulePullbackDerived

/-- `moduleDerivedComponent n` is derived module pullback along `g_n`. -/
theorem moduleDerivedComponent_eq (n : SimplexCategory) :
    moduleDerivedComponent C J O n = (stageMorphism C J O n).modulePullbackDerived :=
  rfl

end

/-- Underlying type-valued sheaves identify geometric inverse image along `g_n` with
restriction of the underlying sheaf of `F` along `ofStage C n`. -/
private def moduleInverseImage_underlyingIso
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    (n : SimplexCategory) :
    (Sheaf.InternalModule.ToInternal.underlying
        ((stageMorphism C J O n).toTopos.ringInverseImage.obj
          (totalRingedSite C J O).structureSheaf)).obj
      (((stageMorphism C J O n).toTopos.moduleInverseImage
          (totalRingedSite C J O).structureSheaf).obj F) ≅
    (stageRestrict C J (Type w) n).obj
      ((Sheaf.InternalModule.ToInternal.underlying
          (totalRingedSite C J O).structureSheaf).obj F) :=
  ((stageMorphism C J O n).toTopos.moduleInverseImageForgetIso
      (totalRingedSite C J O).structureSheaf).app F ≪≫
    (inverseImageIso C J n).app
      ((Sheaf.InternalModule.ToInternal.underlying
          (totalRingedSite C J O).structureSheaf).obj F)

/-- Restriction of scalars does not change the underlying type-valued sheaf. -/
private def restrictScalars_underlyingIso (n : SimplexCategory)
    {R R' : Sheaf ((J n).toGrothendieck) RingCat.{w}} (α : R ⟶ R') :
    SheafOfModules.restrictScalars.{w} α ⋙
        Sheaf.InternalModule.ToInternal.underlying R ≅
      Sheaf.InternalModule.ToInternal.underlying R' :=
  Iso.refl _

/-- Geometric inverse image of an `O`-module along the stage inclusion `g_n`. -/
private def moduleInverseImageComponent (n : SimplexCategory) :
    SheafOfModules.{w} (totalRingedSite C J O).structureSheaf ⥤
      SheafOfModules.{w}
        ((stageMorphism C J O n).toTopos.ringInverseImage.obj
          (totalRingedSite C J O).structureSheaf) :=
  (stageMorphism C J O n).toTopos.moduleInverseImage
    (totalRingedSite C J O).structureSheaf

/-- Underlying type-valued comparison of `moduleTransitionDirect`, as a map of sheaves of types
on `C_m`. -/
private def moduleTransitionDirect_underlying {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    (Sheaf.InternalModule.ToInternal.underlying
        ((stageMorphism C J O m).toTopos.ringInverseImage.obj
          (totalRingedSite C J O).structureSheaf)).obj
      ((moduleInverseImageComponent C J O m).obj F) ⟶
    (Sheaf.InternalModule.ToInternal.underlying
        ((stageMorphism C J O m).toTopos.ringInverseImage.obj
          (totalRingedSite C J O).structureSheaf)).obj
      ((SheafOfModules.restrictScalars.{w}
          (stageMorphism C J O m).structureMap).obj
        ((ringedToposMap C J O φ).modulePushforward.obj
          ((moduleComponent C J O n).obj F))) :=
  (moduleInverseImage_underlyingIso C J O F m).hom ≫
    transitionDirect C J (Type w) φ
      ((Sheaf.InternalModule.ToInternal.underlying
          (totalRingedSite C J O).structureSheaf).obj F) ≫
      ((C.map φ).toFunctor.sheafPushforwardContinuous (Type w)
          (J m).toGrothendieck (J n).toGrothendieck).map
        ((moduleInverseImage_underlyingIso C J O F n).inv ≫
          (Sheaf.InternalModule.ToInternal.underlying
              ((stageMorphism C J O n).toTopos.ringInverseImage.obj
                (totalRingedSite C J O).structureSheaf)).map
            ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction
                (stageMorphism C J O n).structureMap).unit.app
              ((moduleInverseImageComponent C J O n).obj F))) ≫
      (ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O φ)).inv.app
        ((moduleComponent C J O n).obj F) ≫
      (restrictScalars_underlyingIso C J m
          (stageMorphism C J O m).structureMap).inv.app
        ((ringedToposMap C J O φ).modulePushforward.obj
          ((moduleComponent C J O n).obj F))

namespace Module

/-- The underlying direct comparison preserves addition and scalar multiplication. -/
private theorem moduleTransitionDirect_linear {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    let R := (stageMorphism C J O m).toTopos.ringInverseImage.obj
      (totalRingedSite C J O).structureSheaf
    let M := (moduleInverseImageComponent C J O m).obj F
    let α := moduleTransitionDirect_underlying C J O φ F
    (∀ U (x y : M.val.obj U),
      Sheaf.InternalModule.underlyingApp R α U (x + y) =
        Sheaf.InternalModule.underlyingApp R α U x +
          Sheaf.InternalModule.underlyingApp R α U y) ∧
    (∀ U (r : R.obj.obj U) (x : M.val.obj U),
      Sheaf.InternalModule.underlyingApp R α U (r • x) =
        r • Sheaf.InternalModule.underlyingApp R α U x) :=
  sorry

end Module

/-- Geometric module comparison `g_m⁻¹ F ⟶ (f_φ)_* F_n` over the inverse-image ring of `g_m`. -/
private def moduleTransitionDirect_geom {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    (moduleInverseImageComponent C J O m).obj F ⟶
      (SheafOfModules.restrictScalars.{w}
          (stageMorphism C J O m).structureMap).obj
        ((ringedToposMap C J O φ).modulePushforward.obj
          ((moduleComponent C J O n).obj F)) :=
  Sheaf.InternalModule.homOfUnderlying
    ((stageMorphism C J O m).toTopos.ringInverseImage.obj
      (totalRingedSite C J O).structureSheaf)
    (moduleTransitionDirect_underlying C J O φ F)
    (Module.moduleTransitionDirect_linear C J O φ F).1
    (Module.moduleTransitionDirect_linear C J O φ F).2

/-- Direct-image comparison `F_m ⟶ (f_φ)_* F_n` of `O`-modules, obtained by extending scalars
along the stage structure map and applying the scalar-extension counit. -/
def moduleTransitionDirect {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    (moduleComponent C J O m).obj F ⟶
      (ringedToposMap C J O φ).modulePushforward.obj ((moduleComponent C J O n).obj F) :=
  (SheafOfModules.ChangeOfRings.extendScalars
        (stageMorphism C J O m).structureMap).map
      (moduleTransitionDirect_geom C J O φ F) ≫
    (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
        (stageMorphism C J O m).structureMap).counit.app
      ((ringedToposMap C J O φ).modulePushforward.obj ((moduleComponent C J O n).obj F))

/-- The canonical comparison `F(φ) : f_φ^* F_m ⟶ F_n` of `O`-modules. -/
def moduleTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    (ringedToposMap C J O φ).modulePullback.obj ((moduleComponent C J O m).obj F) ⟶
      (moduleComponent C J O n).obj F :=
  ((ringedToposMap C J O φ).moduleAdjunction.homEquiv
      ((moduleComponent C J O m).obj F) ((moduleComponent C J O n).obj F)).symm
    (moduleTransitionDirect C J O φ F)

/-- The adjunction mate of `moduleTransition` is `moduleTransitionDirect`. -/
theorem moduleTransition_homEquiv {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    ((ringedToposMap C J O φ).moduleAdjunction.homEquiv
        ((moduleComponent C J O m).obj F) ((moduleComponent C J O n).obj F))
      (moduleTransition C J O φ F) =
    moduleTransitionDirect C J O φ F :=
  Equiv.apply_symm_apply _ _

namespace Module

/-- The module restriction comparison is natural in the total module sheaf. -/
private theorem moduleTransition_naturality {m n : SimplexCategory} (φ : m ⟶ n)
    {F G : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf} (f : F ⟶ G) :
    (moduleComponent C J O m ⋙ (ringedToposMap C J O φ).modulePullback).map f ≫
        moduleTransition C J O φ G =
      moduleTransition C J O φ F ≫ (moduleComponent C J O n).map f :=
  sorry

end Module

/-- The module restriction comparisons as a natural transformation. -/
def moduleTransitionNatTrans {m n : SimplexCategory} (φ : m ⟶ n) :
    moduleComponent C J O m ⋙ (ringedToposMap C J O φ).modulePullback ⟶
      moduleComponent C J O n where
  app F := moduleTransition C J O φ F
  naturality _ _ f := Module.moduleTransition_naturality C J O φ f

/-- The module restriction comparison on homotopy categories followed by localization. -/
private def moduleTransitionToDerived {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageMorphism C J O m).modulePullbackHomotopy ⋙
        ToposHom.modulePullbackToDerived (ringedToposMap C J O φ) ⟶
      ToposHom.modulePullbackToDerived (stageMorphism C J O n) := by
  let f := stageMorphism C J O m
  let g := ringedToposMap C J O φ
  let h := stageMorphism C J O n
  let af := ToposHom.modulePullback_additive f
  let ag := ToposHom.modulePullback_additive g
  let ah := ToposHom.modulePullback_additive h
  let ac : (f.modulePullback ⋙ g.modulePullback).Additive :=
    { map_add {X Y} {x y} := by
        change g.modulePullback.map (f.modulePullback.map (x + y)) = _
        rw [af.map_add, ag.map_add]
        rfl }
  exact (Functor.associator _ _ _).inv ≫
    whiskerRight
      ((@Functor.mapHomotopyCategoryCompIso _ _ _ _ _ _ _ _ _ _
          f.modulePullback g.modulePullback (f.modulePullback ⋙ g.modulePullback)
          (Iso.refl _) af ag ac (up ℤ)).hom ≫
        @NatTrans.mapHomotopyCategory _ _ _ _ _ _ _ _ _ ac ah
          (moduleTransitionNatTrans C J O φ) (up ℤ))
      (Hom.moduleLocalization (componentRingedSite C J O n))

section

variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/-- The canonical unbounded derived module restriction comparison. -/
def moduleDerivedTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) :
    (ringedToposMap C J O φ).modulePullbackDerived.obj
        ((moduleDerivedComponent C J O m).obj K) ⟶
      (moduleDerivedComponent C J O n).obj K :=
  ((stageMorphism C J O n).modulePullbackDerived.leftDerivedLift
    ((ToposHom.modulePullbackToDerived (stageMorphism C J O n)).totalLeftDerivedCounit
      (Hom.moduleLocalization (totalRingedSite C J O)) (Hom.ModuleQis (totalRingedSite C J O)))
    (Hom.ModuleQis (totalRingedSite C J O))
    (moduleDerivedComponent C J O m ⋙ (ringedToposMap C J O φ).modulePullbackDerived)
    (Functor.LeftDerived.Composition.iteratedCounit
      ((ToposHom.modulePullbackToDerived (stageMorphism C J O m)).totalLeftDerivedCounit
        (Hom.moduleLocalization (totalRingedSite C J O)) (Hom.ModuleQis (totalRingedSite C J O)))
      ((ToposHom.modulePullbackToDerived (ringedToposMap C J O φ)).totalLeftDerivedCounit
        (Hom.moduleLocalization (componentRingedSite C J O m))
        (Hom.ModuleQis (componentRingedSite C J O m))) ≫
      moduleTransitionToDerived C J O φ)).app K

end

namespace Module

/-- An `O`-module on `C_total` is cartesian when `f_φ^* F_m ⟶ F_n` is an isomorphism for
every simplex operator `φ`. -/
class IsCartesian
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) : Prop where
  /-- Every simplex-operator module comparison `f_φ^* F_m ⟶ F_n` is an isomorphism. -/
  isIso_transition : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsIso (moduleTransition C J O φ F)

/-- Cartesianness of an `O`-module is equivalent to every `f_φ^* F_m ⟶ F_n` being an
isomorphism. -/
theorem isCartesian_iff
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    IsCartesian C J O F ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (moduleTransition C J O φ F) :=
  ⟨fun h ↦ h.isIso_transition, fun h ↦ ⟨h⟩⟩

/-- An `O`-module whose every simplex-operator comparison is an isomorphism is cartesian. -/
instance instIsCartesian_of_isIso
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (moduleTransition C J O φ F)] :
    IsCartesian C J O F where
  isIso_transition := h

/-- Every simplex-operator module comparison of a cartesian `O`-module is an isomorphism. -/
instance instIsIso_moduleTransition
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [IsCartesian C J O F] {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (moduleTransition C J O φ F) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `f_φ^* F_m ≅ F_n` attached to a cartesian `O`-module. -/
def transitionIso (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [IsCartesian C J O F] {m n : SimplexCategory} (φ : m ⟶ n) :
    (ringedToposMap C J O φ).modulePullback.obj ((moduleComponent C J O m).obj F) ≅
      (moduleComponent C J O n).obj F :=
  asIso (moduleTransition C J O φ F)

/-- The forward map of `Module.transitionIso` is `moduleTransition`. -/
theorem transitionIso_hom
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [IsCartesian C J O F] {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso C J O F φ).hom = moduleTransition C J O φ F :=
  rfl

end Module

namespace ModuleDerived

variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/-- An object of `D(O)` is cartesian when `Lf_φ^* K_m ⟶ K_n` is an isomorphism for every
simplex operator `φ`. -/
class IsCartesian
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) : Prop where
  /-- Every derived simplex-operator comparison `Lf_φ^* K_m ⟶ K_n` is an isomorphism. -/
  isIso_transition : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsIso (moduleDerivedTransition C J O φ K)

/-- Cartesianness of an object of `D(O)` is equivalent to every `Lf_φ^* K_m ⟶ K_n` being an
isomorphism. -/
theorem isCartesian_iff (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) :
    IsCartesian C J O K ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (moduleDerivedTransition C J O φ K) :=
  ⟨fun h ↦ h.isIso_transition, fun h ↦ ⟨h⟩⟩

/-- An object of `D(O)` whose every derived simplex-operator comparison is an isomorphism is
cartesian. -/
instance instModuleDerivedIsCartesian_of_isIso
    (K : ModuleDerived.{w} (totalRingedSite C J O))
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      IsIso (moduleDerivedTransition C J O φ K)] :
    IsCartesian C J O K where
  isIso_transition := h

/-- Every derived simplex-operator comparison of a cartesian object of `D(O)` is an
isomorphism. -/
instance instIsIso_moduleDerivedTransition
    (K : ModuleDerived.{w} (totalRingedSite C J O))
    [IsCartesian C J O K] {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (moduleDerivedTransition C J O φ K) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `Lf_φ^* K_m ≅ K_n` attached to a cartesian object of `D(O)`. -/
def transitionIso (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [IsCartesian C J O K] {m n : SimplexCategory} (φ : m ⟶ n) :
    (ringedToposMap C J O φ).modulePullbackDerived.obj
        ((moduleDerivedComponent C J O m).obj K) ≅
      (moduleDerivedComponent C J O n).obj K :=
  asIso (moduleDerivedTransition C J O φ K)

/-- The forward map of `ModuleDerived.transitionIso` is `moduleDerivedTransition`. -/
theorem transitionIso_hom (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [IsCartesian C J O K] {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso C J O K φ).hom = moduleDerivedTransition C J O φ K :=
  rfl

end ModuleDerived

end CategoryTheory.SimplicialSites
