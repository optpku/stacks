/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Modules
public import ReasLib.CategoryTheory.Sites.Pushforward.SmallSectionsAdjunction
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Sheaf.InternalModule
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

-- Local instance justification (defeq pin): underlying module comparisons must use the canonical original-coefficient ring-sheaf composition law of the associated fppf topology.
attribute [local instance 2000] associatedTopology_hasSheafCompose

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- Continuous inverse image of fppf modules has continuous precomposition as
its underlying type-valued sheaf functor. -/
def fppfModuleInverseImageUnderlyingIso (f : X ⟶ Y) :
    fppfModuleInverseImage f ⋙
        (@ToInternal.underlying.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose X StandardTopology.fppf)
        (associatedRingedSite X StandardTopology.fppf).structureSheaf) ≅
      (@ToInternal.underlying.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
        (associatedRingedSite Y StandardTopology.fppf).structureSheaf) ⋙
        (toFunctor f).sheafPushforwardContinuous (Type u)
          (X.associatedTopology StandardTopology.fppf)
          (Y.associatedTopology StandardTopology.fppf) :=
  Iso.refl _

private theorem underlying_map_injective {C : Type*} [Category* C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget RingCat.{u})]
    (R : Sheaf J RingCat.{u}) {M N : SheafOfModules.{u} R} {g h : M ⟶ N}
    (e : (ToInternal.underlying R).map g = (ToInternal.underlying R).map h) : g = h := by
  ext U x
  exact congrArg (fun k ↦ k.hom.app U x) e

private theorem underlying_map_homOfUnderlying {C : Type*} [Category* C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget RingCat.{u})]
    (R : Sheaf J RingCat.{u}) {M N : SheafOfModules.{u} R}
    (α : (ToInternal.underlying R).obj M ⟶ (ToInternal.underlying R).obj N)
    (ha : ∀ U (x y : M.val.obj U),
      underlyingApp R α U (x + y) = underlyingApp R α U x + underlyingApp R α U y)
    (hs : ∀ U (r : R.obj.obj U) (x : M.val.obj U),
      underlyingApp R α U (r • x) = r • underlyingApp R α U x) :
    (ToInternal.underlying R).map (homOfUnderlying R α ha hs) = α := by
  ext U x
  rfl

namespace fppfModuleAdjunction

variable (f : X ⟶ Y) [HasSmallAssociatedTypeSections f StandardTopology.fppf]

/-- The forward sheaf mate is the continuous-precomposition adjoint transpose,
transported through the canonical underlying-sheaf comparisons. -/
def mateUnderlying (M : fppfModules Y) (N : fppfModules X)
    (h : (fppfModuleInverseImage f).obj M ⟶ N) :
    ((@ToInternal.underlying.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
        (associatedRingedSite Y StandardTopology.fppf).structureSheaf)).obj M ⟶
      ((@ToInternal.underlying.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
        (associatedRingedSite Y StandardTopology.fppf).structureSheaf)).obj
        ((fppfModulePushforward f).obj N) :=
  ((toFunctor f).sheafPushforwardOfSmallSectionsAdjunction.{u + 1, u, u + 1, u, u}
      (X.associatedTopology StandardTopology.fppf)
      (Y.associatedTopology StandardTopology.fppf)).homEquiv _ _
    ((fppfModuleInverseImageUnderlyingIso f).inv.app M ≫
      ((@ToInternal.underlying.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose X StandardTopology.fppf)
        (associatedRingedSite X StandardTopology.fppf).structureSheaf)).map h) ≫
    (@RingedSite.ToposHom.ModulePushforward.forgetIso.{u + 1, u, u + 1, u, u}
      (associatedRingedSite X StandardTopology.fppf) (associatedRingedSite Y StandardTopology.fppf)
      (associatedTopology_hasSheafCompose X StandardTopology.fppf)
      (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
      (associatedRingedToposHom f StandardTopology.fppf)).inv.app N

/-- The reverse sheaf mate is the inverse adjoint transpose through the same
canonical underlying-sheaf comparisons. -/
def unmateUnderlying (M : fppfModules Y) (N : fppfModules X)
    (g : M ⟶ (fppfModulePushforward f).obj N) :
    ((@ToInternal.underlying.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose X StandardTopology.fppf)
        (associatedRingedSite X StandardTopology.fppf).structureSheaf)).obj
        ((fppfModuleInverseImage f).obj M) ⟶
      ((@ToInternal.underlying.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose X StandardTopology.fppf)
        (associatedRingedSite X StandardTopology.fppf).structureSheaf)).obj N :=
  (fppfModuleInverseImageUnderlyingIso f).hom.app M ≫
    (((toFunctor f).sheafPushforwardOfSmallSectionsAdjunction.{u + 1, u, u + 1, u, u}
      (X.associatedTopology StandardTopology.fppf)
      (Y.associatedTopology StandardTopology.fppf)).homEquiv _ _).symm
      (((@ToInternal.underlying.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
        (associatedRingedSite Y StandardTopology.fppf).structureSheaf)).map g ≫
        (@RingedSite.ToposHom.ModulePushforward.forgetIso.{u + 1, u, u + 1, u, u}
          (associatedRingedSite X StandardTopology.fppf)
          (associatedRingedSite Y StandardTopology.fppf)
          (associatedTopology_hasSheafCompose X StandardTopology.fppf)
          (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
          (associatedRingedToposHom f StandardTopology.fppf)).hom.app N)

/-- The forward sheaf mate preserves addition of module sections. -/
theorem mateUnderlying_add (M : fppfModules Y) (N : fppfModules X)
    (h : (fppfModuleInverseImage f).obj M ⟶ N) :
    ∀ U (x y : M.val.obj U),
      @underlyingApp.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
        (associatedRingedSite Y StandardTopology.fppf).structureSheaf _ _ (mateUnderlying f M N h) U (x + y) =
        @underlyingApp.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
        (associatedRingedSite Y StandardTopology.fppf).structureSheaf _ _ (mateUnderlying f M N h) U x +
          @underlyingApp.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
        (associatedRingedSite Y StandardTopology.fppf).structureSheaf _ _ (mateUnderlying f M N h) U y := sorry

/-- The forward sheaf mate preserves scalar multiplication of module sections. -/
theorem mateUnderlying_smul (M : fppfModules Y) (N : fppfModules X)
    (h : (fppfModuleInverseImage f).obj M ⟶ N) :
    ∀ U (r : (associatedRingedSite Y StandardTopology.fppf).structureSheaf.obj.obj U)
      (x : M.val.obj U),
      @underlyingApp.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
        (associatedRingedSite Y StandardTopology.fppf).structureSheaf _ _ (mateUnderlying f M N h) U (r • x) =
        r • @underlyingApp.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
        (associatedRingedSite Y StandardTopology.fppf).structureSheaf _ _ (mateUnderlying f M N h) U x := sorry

/-- The reverse sheaf mate preserves addition of module sections. -/
theorem unmateUnderlying_add (M : fppfModules Y) (N : fppfModules X)
    (g : M ⟶ (fppfModulePushforward f).obj N) :
    ∀ U (x y : ((fppfModuleInverseImage f).obj M).val.obj U),
      @underlyingApp.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose X StandardTopology.fppf)
        (associatedRingedSite X StandardTopology.fppf).structureSheaf _ _ (unmateUnderlying f M N g) U (x + y) =
        @underlyingApp.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose X StandardTopology.fppf)
        (associatedRingedSite X StandardTopology.fppf).structureSheaf _ _ (unmateUnderlying f M N g) U x +
          @underlyingApp.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose X StandardTopology.fppf)
        (associatedRingedSite X StandardTopology.fppf).structureSheaf _ _ (unmateUnderlying f M N g) U y := sorry

/-- The reverse sheaf mate preserves scalar multiplication of module sections. -/
theorem unmateUnderlying_smul (M : fppfModules Y) (N : fppfModules X)
    (g : M ⟶ (fppfModulePushforward f).obj N) :
    ∀ U (r : (associatedRingedSite X StandardTopology.fppf).structureSheaf.obj.obj U)
      (x : ((fppfModuleInverseImage f).obj M).val.obj U),
      @underlyingApp.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose X StandardTopology.fppf)
        (associatedRingedSite X StandardTopology.fppf).structureSheaf _ _ (unmateUnderlying f M N g) U (r • x) =
        r • @underlyingApp.{u + 1, u, u} _ _ _
        (associatedTopology_hasSheafCompose X StandardTopology.fppf)
        (associatedRingedSite X StandardTopology.fppf).structureSheaf _ _ (unmateUnderlying f M N g) U x := sorry

/-- The forward module mate lifts the specified additive and linear sheaf mate. -/
def mate (M : fppfModules Y) (N : fppfModules X)
    (h : (fppfModuleInverseImage f).obj M ⟶ N) :
    M ⟶ (fppfModulePushforward f).obj N :=
  @homOfUnderlying.{u + 1, u, u} _ _ _
    (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
    (associatedRingedSite Y StandardTopology.fppf).structureSheaf _ _ (mateUnderlying f M N h)
    (mateUnderlying_add f M N h) (mateUnderlying_smul f M N h)

/-- The reverse module mate lifts the specified additive and linear sheaf mate. -/
def unmate (M : fppfModules Y) (N : fppfModules X)
    (g : M ⟶ (fppfModulePushforward f).obj N) :
    (fppfModuleInverseImage f).obj M ⟶ N :=
  @homOfUnderlying.{u + 1, u, u} _ _ _
    (associatedTopology_hasSheafCompose X StandardTopology.fppf)
    (associatedRingedSite X StandardTopology.fppf).structureSheaf _ _ (unmateUnderlying f M N g)
    (unmateUnderlying_add f M N g) (unmateUnderlying_smul f M N g)

set_option backward.isDefEq.respectTransparency false in
/-- Transposing a module map and transposing back recovers that map. -/
theorem homEquiv_left_inv (M : fppfModules Y) (N : fppfModules X) :
    Function.LeftInverse (unmate f M N) (mate f M N) := by
  intro h
  apply @underlying_map_injective _ _ _
    (associatedTopology_hasSheafCompose X StandardTopology.fppf)
    (associatedRingedSite X StandardTopology.fppf).structureSheaf
  simp only [unmate, mate, underlying_map_homOfUnderlying, unmateUnderlying,
    mateUnderlying, Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id, Equiv.symm_apply_apply,
    Iso.hom_inv_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Transposing back and then transposing a module map recovers that map. -/
theorem homEquiv_right_inv (M : fppfModules Y) (N : fppfModules X) :
    Function.RightInverse (unmate f M N) (mate f M N) := by
  intro g
  apply @underlying_map_injective _ _ _
    (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
    (associatedRingedSite Y StandardTopology.fppf).structureSheaf
  simp only [mate, unmate, underlying_map_homOfUnderlying, mateUnderlying,
    unmateUnderlying]
  erw [Iso.inv_hom_id_app_assoc, Equiv.apply_symm_apply, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id]

/-- Module inverse image and direct image have the canonical mate Hom equivalence. -/
def homEquiv (M : fppfModules Y) (N : fppfModules X) :
    ((fppfModuleInverseImage f).obj M ⟶ N) ≃ (M ⟶ (fppfModulePushforward f).obj N) where
  toFun := mate f M N
  invFun := unmate f M N
  left_inv := homEquiv_left_inv f M N
  right_inv := homEquiv_right_inv f M N

set_option backward.isDefEq.respectTransparency false in
/-- The inverse module mate is natural in the source module. -/
theorem homEquiv_naturality_left_symm {M M' : fppfModules Y}
    (g : M' ⟶ M) (N : fppfModules X) (h : M ⟶ (fppfModulePushforward f).obj N) :
    (homEquiv f M' N).symm (g ≫ h) =
      (fppfModuleInverseImage f).map g ≫ (homEquiv f M N).symm h := by
  apply @underlying_map_injective _ _ _
    (associatedTopology_hasSheafCompose X StandardTopology.fppf)
    (associatedRingedSite X StandardTopology.fppf).structureSheaf
  let U := @ToInternal.underlying.{u + 1, u, u} _ _ _
    (associatedTopology_hasSheafCompose X StandardTopology.fppf)
    (associatedRingedSite X StandardTopology.fppf).structureSheaf
  change U.map (unmate f M' N (g ≫ h)) =
    U.map ((fppfModuleInverseImage f).map g ≫ unmate f M N h)
  dsimp only [U]
  simp only [unmate, underlying_map_homOfUnderlying, Functor.map_comp, unmateUnderlying,
    Category.assoc, Adjunction.homEquiv_naturality_left_symm]
  erw [← Category.assoc, ← (fppfModuleInverseImageUnderlyingIso f).hom.naturality g]

set_option backward.isDefEq.respectTransparency false in
/-- The forward module mate is natural in the target module. -/
theorem homEquiv_naturality_right (M : fppfModules Y) {N N' : fppfModules X}
    (h : (fppfModuleInverseImage f).obj M ⟶ N) (g : N ⟶ N') :
    homEquiv f M N' (h ≫ g) =
      homEquiv f M N h ≫ (fppfModulePushforward f).map g := by
  apply @underlying_map_injective _ _ _
    (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
    (associatedRingedSite Y StandardTopology.fppf).structureSheaf
  let U := @ToInternal.underlying.{u + 1, u, u} _ _ _
    (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
    (associatedRingedSite Y StandardTopology.fppf).structureSheaf
  change U.map (mate f M N' (h ≫ g)) =
    U.map (mate f M N h ≫ (fppfModulePushforward f).map g)
  dsimp only [U]
  simp only [mate, underlying_map_homOfUnderlying, Functor.map_comp, mateUnderlying,
    ← Category.assoc, Adjunction.homEquiv_naturality_right]
  simp only [Category.assoc]
  erw [(@RingedSite.ToposHom.ModulePushforward.forgetIso.{u + 1, u, u + 1, u, u}
    (associatedRingedSite X StandardTopology.fppf)
    (associatedRingedSite Y StandardTopology.fppf)
    (associatedTopology_hasSheafCompose X StandardTopology.fppf)
    (associatedTopology_hasSheafCompose Y StandardTopology.fppf)
    (associatedRingedToposHom f StandardTopology.fppf)).inv.naturality g]
  rfl

end fppfModuleAdjunction

/-- Continuous inverse image of fppf modules is left adjoint to small-section
direct image along a morphism of categories fibred in groupoids. -/
def fppfModuleAdjunction (f : X ⟶ Y)
    [HasSmallAssociatedTypeSections f StandardTopology.fppf] :
    fppfModuleInverseImage f ⊣ fppfModulePushforward f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fppfModuleAdjunction.homEquiv f
      homEquiv_naturality_left_symm := fun g h =>
        fppfModuleAdjunction.homEquiv_naturality_left_symm f g _ h
      homEquiv_naturality_right := fun h g =>
        fppfModuleAdjunction.homEquiv_naturality_right f _ h g }

end AlgebraicGeometry.AlgebraicStack
