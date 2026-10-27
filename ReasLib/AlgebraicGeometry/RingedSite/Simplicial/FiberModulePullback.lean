/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Fiber
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ModulePullback

/-!
# Module pullback comparisons for fiberwise simplicial ringed sites
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open Sheaf.InternalModule (underlyingApp)

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

variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]

/-- Underlying type-valued sheaves identify the composite of module pushforwards along
`fiberRingedToposMap ψ` and `fiberRingedToposMap φ` with module pushforward along `fiberRingedToposMap (ψ ≫ φ)`. -/
def ringedModulePushforwardCompUnderlyingIso {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    ((fiberRingedToposMap F J O φ).modulePushforward ⋙
        (fiberRingedToposMap F J O ψ).modulePushforward) ⋙
      Sheaf.InternalModule.ToInternal.underlying
        (fiberComponentRingedSite F J O l).structureSheaf ≅
      (fiberRingedToposMap F J O (ψ ≫ φ)).modulePushforward ⋙
        Sheaf.InternalModule.ToInternal.underlying
          (fiberComponentRingedSite F J O l).structureSheaf :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (fiberRingedToposMap F J O φ).modulePushforward
      (ToposHom.ModulePushforward.forgetIso (fiberRingedToposMap F J O ψ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ToposHom.ModulePushforward.forgetIso (fiberRingedToposMap F J O φ))
      (fiberRingedToposMap F J O ψ).toTopos.pushforward ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.ToInternal.underlying
        (fiberComponentRingedSite F J O n).structureSheaf)
      (toposMap_pushforward_comp F J ψ φ) ≪≫
    (ToposHom.ModulePushforward.forgetIso (fiberRingedToposMap F J O (ψ ≫ φ))).symm

/-- The underlying pushforward comparison preserves addition of sections. -/
theorem ringedModulePushforwardCompIso_add {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    ∀ M,
    let R := (fiberComponentRingedSite F J O l).structureSheaf
    let A := (((fiberRingedToposMap F J O φ).modulePushforward ⋙
          (fiberRingedToposMap F J O ψ).modulePushforward)).obj M
    let α := (ringedModulePushforwardCompUnderlyingIso F J O ψ φ).hom.app M
    ∀ U (x y : A.val.obj U),
      underlyingApp R α U (x + y) = underlyingApp R α U x + underlyingApp R α U y := sorry

/-- The underlying pushforward comparison preserves scalar multiplication of sections. -/
theorem ringedModulePushforwardCompIso_smul {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    ∀ M,
    let R := (fiberComponentRingedSite F J O l).structureSheaf
    let A := (((fiberRingedToposMap F J O φ).modulePushforward ⋙
          (fiberRingedToposMap F J O ψ).modulePushforward)).obj M
    let α := (ringedModulePushforwardCompUnderlyingIso F J O ψ φ).hom.app M
    ∀ U (a : R.obj.obj U) (x : A.val.obj U),
      underlyingApp R α U (a • x) = a • underlyingApp R α U x := sorry

/-- Module pushforwards along `fiberRingedToposMap` compose as `f_{ψ ≫ φ,*}`. -/
def ringedModulePushforwardCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (fiberRingedToposMap F J O φ).modulePushforward ⋙
      (fiberRingedToposMap F J O ψ).modulePushforward ≅
      (fiberRingedToposMap F J O (ψ ≫ φ)).modulePushforward :=
  Sheaf.InternalModule.functorIsoOfUnderlying _
    (ringedModulePushforwardCompUnderlyingIso F J O ψ φ)
    (ringedModulePushforwardCompIso_add F J O ψ φ)
    (ringedModulePushforwardCompIso_smul F J O ψ φ)

/-- Underived module pullbacks along `fiberRingedToposMap` compose as `f_{ψ ≫ φ}^*`. -/
def ringedModulePullbackCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (fiberRingedToposMap F J O (ψ ≫ φ)).modulePullback ≅
      (fiberRingedToposMap F J O ψ).modulePullback ⋙
        (fiberRingedToposMap F J O φ).modulePullback :=
  (Adjunction.leftAdjointCompIso
      (fiberRingedToposMap F J O ψ).moduleAdjunction
      (fiberRingedToposMap F J O φ).moduleAdjunction
      (fiberRingedToposMap F J O (ψ ≫ φ)).moduleAdjunction
      (ringedModulePushforwardCompIso F J O ψ φ)).symm

/-- Underlying type-valued sheaves identify module pushforward along `fiberRingedToposMap (𝟙 n)`
with the identity. -/
def ringedModulePushforwardIdUnderlyingIso (n : SimplexCategory) :
    (fiberRingedToposMap F J O (𝟙 n)).modulePushforward ⋙
      Sheaf.InternalModule.ToInternal.underlying
        (fiberComponentRingedSite F J O n).structureSheaf ≅
      𝟭 (SheafOfModules.{w} (fiberComponentRingedSite F J O n).structureSheaf) ⋙
        Sheaf.InternalModule.ToInternal.underlying
          (fiberComponentRingedSite F J O n).structureSheaf :=
  ToposHom.ModulePushforward.forgetIso (fiberRingedToposMap F J O (𝟙 n)) ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.ToInternal.underlying
        (fiberComponentRingedSite F J O n).structureSheaf)
      (Functor.sheafPushforwardCocontinuousIso
          (J (op n)).toGrothendieck (J (op n)).toGrothendieck
          (F.map (𝟙 n).op).toFunctor (u' := 𝟭 (F.obj (op n)))
          (Cat.Hom.toNatIso (eqToIso (F.map_id (op n))) :
            (F.map (𝟙 n).op).toFunctor ≅ 𝟭 (F.obj (op n))) ≪≫
        Functor.sheafPushforwardCocontinuousId (Type w) (J (op n)).toGrothendieck) ≪≫
    (Functor.rightUnitor _).symm

/-- The underlying pushforward comparison preserves addition of sections. -/
theorem ringedModulePushforwardIdIso_add (n : SimplexCategory) :
    ∀ M,
    let R := (fiberComponentRingedSite F J O n).structureSheaf
    let A := ((fiberRingedToposMap F J O (𝟙 n)).modulePushforward).obj M
    let α := (ringedModulePushforwardIdUnderlyingIso F J O n).hom.app M
    ∀ U (x y : A.val.obj U),
      underlyingApp R α U (x + y) = underlyingApp R α U x + underlyingApp R α U y := sorry

/-- The underlying pushforward comparison preserves scalar multiplication of sections. -/
theorem ringedModulePushforwardIdIso_smul (n : SimplexCategory) :
    ∀ M,
    let R := (fiberComponentRingedSite F J O n).structureSheaf
    let A := ((fiberRingedToposMap F J O (𝟙 n)).modulePushforward).obj M
    let α := (ringedModulePushforwardIdUnderlyingIso F J O n).hom.app M
    ∀ U (a : R.obj.obj U) (x : A.val.obj U),
      underlyingApp R α U (a • x) = a • underlyingApp R α U x := sorry

/-- Module pushforward along `fiberRingedToposMap (𝟙 n)` is the identity. -/
def ringedModulePushforwardIdIso (n : SimplexCategory) :
    (fiberRingedToposMap F J O (𝟙 n)).modulePushforward ≅
      𝟭 (SheafOfModules.{w} (fiberComponentRingedSite F J O n).structureSheaf) :=
  Sheaf.InternalModule.functorIsoOfUnderlying _
    (ringedModulePushforwardIdUnderlyingIso F J O n)
    (ringedModulePushforwardIdIso_add F J O n)
    (ringedModulePushforwardIdIso_smul F J O n)

/-- Underived module pullback along `fiberRingedToposMap (𝟙 n)` is the identity. -/
def ringedModulePullbackIdIso (n : SimplexCategory) :
    (fiberRingedToposMap F J O (𝟙 n)).modulePullback ≅
      𝟭 (SheafOfModules.{w} (fiberComponentRingedSite F J O n).structureSheaf) :=
  Adjunction.leftAdjointIdIso
    (fiberRingedToposMap F J O (𝟙 n)).moduleAdjunction
    (ringedModulePushforwardIdIso F J O n)

/-- The canonical module-pullback comparisons for the component ringed sites. -/
def modulePullbackFunctoriality :
    RingedSite.Simplicial.ModulePullbackFunctoriality
      (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) where
  pullbackCompIso := ringedModulePullbackCompIso F J O
  pullbackIdIso := ringedModulePullbackIdIso F J O

end CategoryTheory.Grothendieck
