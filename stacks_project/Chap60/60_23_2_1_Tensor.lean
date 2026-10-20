/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Pushforward
public import stacks_project.Chap60.«60_23_2_1_Eval»
public import stacks_project.Chap60.Lemma_60_12_3

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CategoryTheory.MonoidalCategory
open CrystallineModuleSheaf
open PresheafOfModules.Monoidal

@[expose] public section

universe u

variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- Presheaves of modules on a scheme inherit the presheaf-of-modules monoidal structure. -/
noncomputable instance (Y : Scheme.{u}) :
    MonoidalCategory (PresheafOfModules.{u} Y.ringCatSheaf.obj) :=
  inferInstanceAs
    (MonoidalCategory (PresheafOfModules.{u} (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

/-- Tensor product of module sheaves on a scheme. -/
noncomputable def tensorOnScheme {Y : Scheme.{u}} (N M : Y.Modules) : Y.Modules where
  val := N.val ⊗ M.val
  isSheaf := sorry

/-- The tensor product of module sheaves is the objectwise presheaf tensor product. -/
theorem tensorOnScheme_val {Y : Scheme.{u}} (N M : Y.Modules) :
    (tensorOnScheme N M).val = N.val ⊗ M.val := sorry

/-- Tensor product of morphisms of module sheaves. -/
noncomputable def tensorOnScheme_hom {Y : Scheme.{u}}
    {N₁ N₂ M₁ M₂ : Y.Modules} (f : N₁ ⟶ N₂) (g : M₁ ⟶ M₂) :
    tensorOnScheme N₁ M₁ ⟶ tensorOnScheme N₂ M₂ :=
  ⟨f.val ⊗ₘ g.val⟩

/-- Tensoring a morphism on the right with a fixed module sheaf. -/
noncomputable def tensorOnScheme_map {Y : Scheme.{u}} (N : Y.Modules)
    {M₁ M₂ : Y.Modules} (f : M₁ ⟶ M₂) :
    tensorOnScheme N M₁ ⟶ tensorOnScheme N M₂ :=
  tensorOnScheme_hom (𝟙 N) f

/-- Right tensoring with `N` applies `tensorHom` of the identity on `N`. -/
theorem tensorOnScheme_map_val {Y : Scheme.{u}} (N : Y.Modules)
    {M₁ M₂ : Y.Modules} (f : M₁ ⟶ M₂) :
    (tensorOnScheme_map N f).val = (𝟙 N.val) ⊗ₘ f.val := sorry

/-- Lax comparison from the tensor of pushforwards to the pushforward of a tensor. -/
noncomputable def tensorOnScheme_pushforward {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (N M : Y.Modules) :
    tensorOnScheme ((Scheme.Modules.pushforward f).obj N)
      ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward f).obj (tensorOnScheme N M) :=
  ⟨PresheafOfModules.Pushforward.tensorComparison
      (TopologicalSpace.Opens.map f.base) f.c N.val M.val⟩

/-- Canonical oplax comparison from the pullback of a tensor to the tensor of pullbacks. -/
noncomputable def tensorOnScheme_pullback {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (N M : Z.Modules) :
    (Scheme.Modules.pullback f).obj (tensorOnScheme N M) ⟶
      tensorOnScheme ((Scheme.Modules.pullback f).obj N)
        ((Scheme.Modules.pullback f).obj M) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (tensorOnScheme_hom
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      tensorOnScheme_pushforward f ((Scheme.Modules.pullback f).obj N)
        ((Scheme.Modules.pullback f).obj M))

/-- Pullback of a tensor of module sheaves identifies with the tensor of the pullbacks. -/
theorem tensorOnScheme_pullback_eq {Y Z : Scheme.{u}} (f : Y ⟶ Z) (N M : Z.Modules) :
    (Scheme.Modules.pullback f).obj (tensorOnScheme N M) =
      tensorOnScheme ((Scheme.Modules.pullback f).obj N)
        ((Scheme.Modules.pullback f).obj M) := sorry

/-- Tensor of a module on `T` with the restricted crystal `F.obj T`. -/
noncomputable def crystallineRestrictionTensor
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (M : (T.obj.1.thickening).Modules) :
    (T.obj.1.thickening).Modules :=
  tensorOnScheme (crystallineEval F T) M

/-- Tensoring with `F.obj T` is the module-sheaf tensor product. -/
theorem crystallineRestrictionTensor_obj
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (M : (T.obj.1.thickening).Modules) :
    crystallineRestrictionTensor F T M =
      tensorOnScheme (F.obj T) M := sorry

/-- Comparison of `F ⊗ Ω_{X/S}` along a morphism of small crystalline objects,
obtained by tensoring `F.comparison` with `Ω_XS.module.comparison`. -/
noncomputable def crystallineDeRhamComparison
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    {p : ℕ} [Fact (Nat.Prime p)]
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
    {h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))}
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    {A B : smallCrystallineSite S I γ h_compatible X x₀} (f : A ⟶ B) :
    (Scheme.Modules.pullback f.hom.thickening).obj
        (tensorOnScheme (F.obj B) (Ω_XS.module.obj B.obj.1)) ⟶
      tensorOnScheme (F.obj A) (Ω_XS.module.obj A.obj.1) :=
  tensorOnScheme_pullback f.hom.thickening (F.obj B) (Ω_XS.module.obj B.obj.1) ≫
    tensorOnScheme_hom (F.comparison f) (Ω_XS.module.comparison f.hom)
