/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.Cartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Fiber
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Left

/-!
# Cartesian modules on a fiberwise simplicial ringed site

Canonical module restriction comparisons and their unbounded left-derived lifts.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor RingedSite ComplexShape
open RingedSite.Hom (ModuleDerived)

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})

variable [UnivLE.{max u v, w}]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]

/-- Restriction of a total module sheaf to a fiber as canonical module pullback. -/
def moduleComponent (n : SimplexCategory) :
    SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf ⥤
      SheafOfModules.{w} (fiberComponentRingedSite F J O n).structureSheaf :=
  (fiberStageMorphism F J O n).modulePullback

section

variable [∀ n, ToposHom.HasModulePullbackDerived (fiberStageMorphism F J O n)]

/-- Unbounded derived restriction of a total module object to a fiber. -/
def moduleDerivedComponent (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O) ⥤
      Hom.ModuleDerived.{w} (fiberComponentRingedSite F J O n) :=
  (fiberStageMorphism F J O n).modulePullbackDerived

end

/-- The `ιNatTrans` 2-cell on underlying type-valued sheaves of `F_m` and `F_n`. -/
private def moduleTransition_underlying {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} O) :
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck).obj
      ((Sheaf.InternalModule.ToInternal.underlying
          (fiberComponentRingSheaf F J O m)).obj
        ((fiberStageMorphism F J O m).modulePullback.obj M)) ⟶
      ((ι F (op n)).sheafPushforwardContinuous (Type w)
        (J (op n)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M) :=
  (presheafToSheaf ((J (op n)).toGrothendieck) (Type w)).map
      (whiskerLeft (F.map φ.op).toFunctor.op
        ((sheafToPresheaf ((J (op m)).toGrothendieck) (Type w)).map
          (fiberModulePullback_underlyingIso F J O m M).hom)) ≫
    (presheafToSheaf ((J (op n)).toGrothendieck) (Type w)).map
      (whiskerRight (NatTrans.op (ιNatTrans φ.op))
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M).obj) ≫
    (sheafificationAdjunction ((J (op n)).toGrothendieck) (Type w)).counit.app
      (((ι F (op n)).sheafPushforwardContinuous (Type w)
          (J (op n)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M))

/-- The fixed underlying fiber comparison preserves addition and scalar multiplication. -/
private theorem moduleTransition_linear {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} O) :
    let R := (fiberRingedToposMap F J O φ).toTopos.ringInverseImage.obj
      (fiberComponentRingSheaf F J O m)
    let A := ((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
      (fiberComponentRingSheaf F J O m)).obj
        ((fiberStageMorphism F J O m).modulePullback.obj M)
    let B := (SheafOfModules.restrictScalars
      (fiberRingedToposMap F J O φ).structureMap).obj
        ((fiberStageMorphism F J O n).modulePullback.obj M)
    let α : (Sheaf.InternalModule.ToInternal.underlying R).obj A ⟶
        (Sheaf.InternalModule.ToInternal.underlying R).obj B :=
      ((fiberRingedToposMap F J O φ).toTopos.moduleInverseImageForgetIso
          (fiberComponentRingSheaf F J O m)).hom.app
          ((fiberStageMorphism F J O m).modulePullback.obj M) ≫
        moduleTransition_underlying F J O φ M ≫
        (fiberModulePullback_underlyingIso F J O n M).inv ≫
        (fiberRingedToposMap_restrictScalars_forgetIso F J O φ
            ((fiberStageMorphism F J O n).modulePullback.obj M)).inv
    (∀ U (x y : A.val.obj U),
      Sheaf.InternalModule.underlyingApp R α U (x + y) =
        Sheaf.InternalModule.underlyingApp R α U x +
          Sheaf.InternalModule.underlyingApp R α U y) ∧
    (∀ U (r : R.obj.obj U) (x : A.val.obj U),
      Sheaf.InternalModule.underlyingApp R α U (r • x) =
        r • Sheaf.InternalModule.underlyingApp R α U x) :=
  sorry

/-- The module-linear geometric inverse-image comparison along a simplex operator. -/
private def moduleTransition_geometric {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} O) :
    ((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
        (fiberComponentRingSheaf F J O m)).obj
      ((fiberStageMorphism F J O m).modulePullback.obj M) ⟶
      (SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).obj
        ((fiberStageMorphism F J O n).modulePullback.obj M) :=
by
  let R := (fiberRingedToposMap F J O φ).toTopos.ringInverseImage.obj
    (fiberComponentRingSheaf F J O m)
  let A := ((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
    (fiberComponentRingSheaf F J O m)).obj
      ((fiberStageMorphism F J O m).modulePullback.obj M)
  let B := (SheafOfModules.restrictScalars
    (fiberRingedToposMap F J O φ).structureMap).obj
      ((fiberStageMorphism F J O n).modulePullback.obj M)
  let α : (Sheaf.InternalModule.ToInternal.underlying R).obj A ⟶
      (Sheaf.InternalModule.ToInternal.underlying R).obj B :=
    ((fiberRingedToposMap F J O φ).toTopos.moduleInverseImageForgetIso
        (fiberComponentRingSheaf F J O m)).hom.app
        ((fiberStageMorphism F J O m).modulePullback.obj M) ≫
      moduleTransition_underlying F J O φ M ≫
      (fiberModulePullback_underlyingIso F J O n M).inv ≫
      (fiberRingedToposMap_restrictScalars_forgetIso F J O φ
          ((fiberStageMorphism F J O n).modulePullback.obj M)).inv
  exact Sheaf.InternalModule.homOfUnderlying R α
    (moduleTransition_linear F J O φ M).1 (moduleTransition_linear F J O φ M).2

/-- Restriction `f_φ^* F_m ⟶ F_n` along the simplicial 2-cell. -/
def moduleTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} O) :
    (fiberRingedToposMap F J O φ).modulePullback.obj
      ((moduleComponent F J O m).obj M) ⟶
      (moduleComponent F J O n).obj M :=
  (ToposHom.ModulePullback.scalarHomEquiv (fiberRingedToposMap F J O φ)
      (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
          (fiberComponentRingSheaf F J O m)).obj
        ((fiberStageMorphism F J O m).modulePullback.obj M))
      ((fiberStageMorphism F J O n).modulePullback.obj M)).symm
    (moduleTransition_geometric F J O φ M)

/-- The module restriction comparison is natural in the total module sheaf. -/
private theorem moduleTransition_naturality {m n : SimplexCategory} (φ : m ⟶ n)
    {M N : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf} (f : M ⟶ N) :
    (moduleComponent F J O m ⋙ (fiberRingedToposMap F J O φ).modulePullback).map f ≫
        moduleTransition F J O φ N =
      moduleTransition F J O φ M ≫ (moduleComponent F J O n).map f :=
  sorry

/-- The module restriction comparisons as a natural transformation. -/
def moduleTransitionNatTrans {m n : SimplexCategory} (φ : m ⟶ n) :
    moduleComponent F J O m ⋙ (fiberRingedToposMap F J O φ).modulePullback ⟶
      moduleComponent F J O n where
  app M := moduleTransition F J O φ M
  naturality _ _ f := moduleTransition_naturality F J O φ f

/-- The module restriction comparison on homotopy categories followed by localization. -/
private def moduleTransitionToDerived {m n : SimplexCategory} (φ : m ⟶ n) :
    (fiberStageMorphism F J O m).modulePullbackHomotopy ⋙
        ToposHom.modulePullbackToDerived (fiberRingedToposMap F J O φ) ⟶
      ToposHom.modulePullbackToDerived (fiberStageMorphism F J O n) := by
  let f := fiberStageMorphism F J O m
  let g := fiberRingedToposMap F J O φ
  let h := fiberStageMorphism F J O n
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
          (moduleTransitionNatTrans F J O φ) (up ℤ))
      (Hom.moduleLocalization (fiberComponentRingedSite F J O n))

section

variable [∀ n, ToposHom.HasModulePullbackDerived (fiberStageMorphism F J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fiberRingedToposMap F J O φ)]

/-- The canonical unbounded derived module restriction comparison. -/
def moduleDerivedTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)) :
    (fiberRingedToposMap F J O φ).modulePullbackDerived.obj
        ((moduleDerivedComponent F J O m).obj K) ⟶
      (moduleDerivedComponent F J O n).obj K :=
  ((fiberStageMorphism F J O n).modulePullbackDerived.leftDerivedLift
    ((ToposHom.modulePullbackToDerived (fiberStageMorphism F J O n)).totalLeftDerivedCounit
      (Hom.moduleLocalization (fiberTotalRingedSite F J O)) (Hom.ModuleQis (fiberTotalRingedSite F J O)))
    (Hom.ModuleQis (fiberTotalRingedSite F J O))
    (moduleDerivedComponent F J O m ⋙ (fiberRingedToposMap F J O φ).modulePullbackDerived)
    (Functor.LeftDerived.Composition.iteratedCounit
      ((ToposHom.modulePullbackToDerived (fiberStageMorphism F J O m)).totalLeftDerivedCounit
        (Hom.moduleLocalization (fiberTotalRingedSite F J O)) (Hom.ModuleQis (fiberTotalRingedSite F J O)))
      ((ToposHom.modulePullbackToDerived (fiberRingedToposMap F J O φ)).totalLeftDerivedCounit
        (Hom.moduleLocalization (fiberComponentRingedSite F J O m))
        (Hom.ModuleQis (fiberComponentRingedSite F J O m))) ≫
      moduleTransitionToDerived F J O φ)).app K

end

namespace Module

/-- An `O`-module on `C_total` is cartesian when `f_φ^* F_m ⟶ F_n` is an isomorphism for
every simplex operator `φ`. -/
class IsCartesian
    (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf) : Prop where
  /-- Every simplex-operator module comparison `f_φ^* F_m ⟶ F_n` is an isomorphism. -/
  isIso_transition : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsIso (moduleTransition F J O φ M)

/-- Cartesianness of an `O`-module is equivalent to every `f_φ^* F_m ⟶ F_n` being an
isomorphism. -/
theorem isCartesian_iff
    (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf) :
    IsCartesian F J O M ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (moduleTransition F J O φ M) :=
  ⟨fun h ↦ h.isIso_transition, fun h ↦ ⟨h⟩⟩

/-- An `O`-module whose every simplex-operator comparison is an isomorphism is cartesian. -/
instance instIsCartesian_of_isIso
    (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf)
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (moduleTransition F J O φ M)] :
    IsCartesian F J O M where
  isIso_transition := h

/-- Every simplex-operator module comparison of a cartesian `O`-module is an isomorphism. -/
instance instIsIso_moduleTransition
    (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf)
    [IsCartesian F J O M] {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (moduleTransition F J O φ M) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `f_φ^* F_m ≅ F_n` attached to a cartesian `O`-module. -/
def transitionIso (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf)
    [IsCartesian F J O M] {m n : SimplexCategory} (φ : m ⟶ n) :
    (fiberRingedToposMap F J O φ).modulePullback.obj ((moduleComponent F J O m).obj M) ≅
      (moduleComponent F J O n).obj M :=
  asIso (moduleTransition F J O φ M)

/-- The forward map of `Module.transitionIso` is `moduleTransition`. -/
theorem transitionIso_hom
    (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf)
    [IsCartesian F J O M] {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso F J O M φ).hom = moduleTransition F J O φ M :=
  rfl

end Module

namespace ModuleDerived

variable [∀ n, ToposHom.HasModulePullbackDerived (fiberStageMorphism F J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fiberRingedToposMap F J O φ)]

/-- An object of `D(O)` is cartesian when `Lf_φ^* K_m ⟶ K_n` is an isomorphism for every
simplex operator `φ`. -/
class IsCartesian
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)) : Prop where
  /-- Every derived simplex-operator comparison `Lf_φ^* K_m ⟶ K_n` is an isomorphism. -/
  isIso_transition : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsIso (moduleDerivedTransition F J O φ K)

/-- Cartesianness of an object of `D(O)` is equivalent to every `Lf_φ^* K_m ⟶ K_n` being an
isomorphism. -/
theorem isCartesian_iff (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)) :
    IsCartesian F J O K ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (moduleDerivedTransition F J O φ K) :=
  ⟨fun h ↦ h.isIso_transition, fun h ↦ ⟨h⟩⟩

/-- An object of `D(O)` whose every derived simplex-operator comparison is an isomorphism is
cartesian. -/
instance instModuleDerivedIsCartesian_of_isIso
    (K : ModuleDerived.{w} (fiberTotalRingedSite F J O))
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      IsIso (moduleDerivedTransition F J O φ K)] :
    IsCartesian F J O K where
  isIso_transition := h

/-- Every derived simplex-operator comparison of a cartesian object of `D(O)` is an
isomorphism. -/
instance instIsIso_moduleDerivedTransition
    (K : ModuleDerived.{w} (fiberTotalRingedSite F J O))
    [IsCartesian F J O K] {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (moduleDerivedTransition F J O φ K) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `Lf_φ^* K_m ≅ K_n` attached to a cartesian object of `D(O)`. -/
def transitionIso (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O))
    [IsCartesian F J O K] {m n : SimplexCategory} (φ : m ⟶ n) :
    (fiberRingedToposMap F J O φ).modulePullbackDerived.obj
        ((moduleDerivedComponent F J O m).obj K) ≅
      (moduleDerivedComponent F J O n).obj K :=
  asIso (moduleDerivedTransition F J O φ K)

/-- The forward map of `ModuleDerived.transitionIso` is `moduleDerivedTransition`. -/
theorem transitionIso_hom (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O))
    [IsCartesian F J O K] {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso F J O K φ).hom = moduleDerivedTransition F J O φ K :=
  rfl

end ModuleDerived

end CategoryTheory.Grothendieck
