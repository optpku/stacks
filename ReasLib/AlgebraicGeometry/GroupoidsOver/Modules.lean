/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedTopos
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Fppf modules and their image functors on categories fibred in groupoids -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Module direct image along an associated ringed-topos morphism is additive. -/
theorem associatedRingedToposHom_modulePushforward_additive {S : Scheme.{u}}
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [HasSmallAssociatedTypeSections f τ] :
    (@RingedSite.ToposHom.modulePushforward.{u + 1, u, u + 1, u, u}
      (associatedRingedSite X τ) (associatedRingedSite Y τ)
      (associatedTopology_hasSheafCompose X τ)
      (associatedTopology_hasSheafCompose Y τ)
      (associatedRingedToposHom f τ)).Additive :=
  @RingedSite.ToposHom.modulePushforward_additive.{u + 1, u, u + 1, u, u}
    (associatedRingedSite X τ) (associatedRingedSite Y τ)
    (associatedTopology_hasSheafCompose X τ)
    (associatedTopology_hasSheafCompose Y τ)
    (associatedRingedToposHom f τ)

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The category of fppf `𝒪_X`-modules on the associated fppf ringed site. -/
abbrev fppfModules (X : GroupoidsOver S) :=
  SheafOfModules.{u} (associatedRingedSite X StandardTopology.fppf).structureSheaf

/-- `fppfModules X` is the category of sheaves of modules on
`associatedRingedSite X StandardTopology.fppf`. -/
theorem fppfModules_eq (X : GroupoidsOver S) :
    fppfModules X =
      SheafOfModules.{u} (associatedRingedSite X StandardTopology.fppf).structureSheaf :=
  rfl

/-- The category of fppf `𝒪_X`-modules is abelian. -/
instance fppfModules_abelian (X : GroupoidsOver S) : Abelian (fppfModules X) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- Inverse image of fppf modules is continuous precomposition with scalar
restriction along the inverse canonical structure-sheaf comparison. -/
def fppfModuleInverseImage {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfModules Y ⥤ fppfModules X :=
  @SheafOfModules.pushforward.{u, u, u, u + 1, u + 1, u}
    _ _ _ _ _ _ _ _ _ (toFunctor_isContinuous f StandardTopology.fppf)
    (associatedStructureSheafInverseImageIso f StandardTopology.fppf).inv

/-- Fppf module inverse image is continuous module pushforward along the
inverse canonical structure-sheaf comparison. -/
theorem fppfModuleInverseImage_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fppfModuleInverseImage f =
      @SheafOfModules.pushforward.{u, u, u, u + 1, u + 1, u}
        _ _ _ _ _ _ _ _ _ (toFunctor_isContinuous f StandardTopology.fppf)
        (associatedStructureSheafInverseImageIso f StandardTopology.fppf).inv :=
  rfl

/-- The underived fppf module pushforward `f_*`, as the concrete module
direct image along `associatedRingedToposHom f StandardTopology.fppf`. -/
def fppfModulePushforward {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallAssociatedTypeSections f StandardTopology.fppf] :
    fppfModules X ⥤ fppfModules Y :=
  @RingedSite.ToposHom.modulePushforward.{u + 1, u, u + 1, u, u}
    (associatedRingedSite X StandardTopology.fppf)
    (associatedRingedSite Y StandardTopology.fppf)
    (associatedTopology_hasSheafCompose X StandardTopology.fppf)
    (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
    (associatedRingedToposHom f StandardTopology.fppf)

/-- `fppfModulePushforward f` is the module direct image of the associated fppf
ringed-topos morphism. -/
theorem fppfModulePushforward_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallAssociatedTypeSections f StandardTopology.fppf] :
    fppfModulePushforward f =
      @RingedSite.ToposHom.modulePushforward.{u + 1, u, u + 1, u, u}
    (associatedRingedSite X StandardTopology.fppf)
    (associatedRingedSite Y StandardTopology.fppf)
    (associatedTopology_hasSheafCompose X StandardTopology.fppf)
    (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
    (associatedRingedToposHom f StandardTopology.fppf) :=
  rfl

/-- Fppf module direct image is additive. -/
theorem fppfModulePushforward_additive {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallAssociatedTypeSections f StandardTopology.fppf] :
    (fppfModulePushforward f).Additive :=
  @RingedSite.ToposHom.modulePushforward_additive.{u + 1, u, u + 1, u, u}
    (associatedRingedSite X StandardTopology.fppf)
    (associatedRingedSite Y StandardTopology.fppf)
    (associatedTopology_hasSheafCompose X StandardTopology.fppf)
    (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
    (associatedRingedToposHom f StandardTopology.fppf)

/-- Fppf modules on a category fibred in groupoids admit injective resolutions. -/
instance instHasInjectiveResolutions_fppfModules (X : GroupoidsOver S) :
    HasInjectiveResolutions (fppfModules X) :=
  sorry

/-- The degree-`i` fppf higher direct image functor `R^i f_*` on fppf modules. -/
abbrev fppfHigherDirectImageFunctor {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallAssociatedTypeSections f StandardTopology.fppf] (i : ℕ) :
    fppfModules X ⥤ fppfModules Y :=
  @Functor.rightDerived _ _ _ _ _ _ _ (fppfModulePushforward f)
    (fppfModulePushforward_additive f) i

/-- `fppfHigherDirectImageFunctor f i` is the degree-`i` right derived functor of
fppf module direct image. -/
theorem fppfHigherDirectImageFunctor_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallAssociatedTypeSections f StandardTopology.fppf] (i : ℕ) :
    fppfHigherDirectImageFunctor f i =
      @Functor.rightDerived _ _ _ _ _ _ _ (fppfModulePushforward f)
        (fppfModulePushforward_additive f) i :=
  rfl

/-- The degree-`i` fppf higher direct image `R^i f_* F`. -/
abbrev fppfHigherDirectImage {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    (F : fppfModules X) (i : ℕ) : fppfModules Y :=
  (fppfHigherDirectImageFunctor f i).obj F

/-- `fppfHigherDirectImage f F i` is the object map of `fppfHigherDirectImageFunctor`. -/
theorem fppfHigherDirectImage_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    (F : fppfModules X) (i : ℕ) :
    fppfHigherDirectImage f F i = (fppfHigherDirectImageFunctor f i).obj F :=
  rfl

end AlgebraicGeometry.AlgebraicStack
