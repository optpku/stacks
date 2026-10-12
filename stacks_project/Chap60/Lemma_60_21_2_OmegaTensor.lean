/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
public import stacks_project.Chap60.Definition_60_11_1_ModuleProperties
public import stacks_project.Chap60.Lemma_60_12_3_Differentials

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf
open PresheafOfModules

noncomputable section

universe u

/-- Tensor product of two `𝒪_X`-modules as the objectwise tensor of underlying
presheaves of modules. -/
def schemeModulesTensor {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  { val :=
      Monoidal.tensorObj (R := X.presheaf)
        ((SheafOfModules.forget X.ringCatSheaf).obj M)
        ((SheafOfModules.forget X.ringCatSheaf).obj N)
    isSheaf := sorry }

/-- Exterior power of an `𝒪_X`-module as the sectionwise exterior-power presheaf. -/
def schemeModulesExteriorPower {X : Scheme.{u}} (M : X.Modules) (i : ℕ) : X.Modules :=
  { val :=
      ExteriorPower.presheaf (𝒪 := X.presheaf)
        ((SheafOfModules.forget X.ringCatSheaf).obj M) i
    isSheaf := sorry }

/-- Pullback of a tensor product of modules is the tensor product of the pullbacks. -/
theorem schemeModules_pullback_tensor {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules) :
    (pullback f).obj (schemeModulesTensor M N) =
      schemeModulesTensor ((pullback f).obj M) ((pullback f).obj N) :=
  sorry

/-- Pullback of an exterior power of modules is the exterior power of the pullback. -/
theorem schemeModules_pullback_exteriorPower {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (i : ℕ) :
    (pullback f).obj (schemeModulesExteriorPower M i) =
      schemeModulesExteriorPower ((pullback f).obj M) i :=
  sorry

/-- Comparison morphism for a tensor of module morphisms along a scheme morphism. -/
def schemeModulesTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} {M' N' : X.Modules}
    (gM : (pullback f).obj M ⟶ M') (gN : (pullback f).obj N ⟶ N') :
    (pullback f).obj (schemeModulesTensor M N) ⟶ schemeModulesTensor M' N' :=
  eqToHom (schemeModules_pullback_tensor f M N) ≫
    ⟨Monoidal.tensorHom (R := X.presheaf)
      ((SheafOfModules.forget X.ringCatSheaf).map gM)
      ((SheafOfModules.forget X.ringCatSheaf).map gN)⟩

/-- Comparison morphism for an exterior power of a module morphism along a scheme morphism. -/
def schemeModulesExteriorPowerComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} {M' : X.Modules} (g : (pullback f).obj M ⟶ M') (i : ℕ) :
    (pullback f).obj (schemeModulesExteriorPower M i) ⟶ schemeModulesExteriorPower M' i :=
  eqToHom (schemeModules_pullback_exteriorPower f M i) ≫
    ⟨ExteriorPower.hom (𝒪 := X.presheaf)
      ((SheafOfModules.forget X.ringCatSheaf).map g) i⟩

/-- Exterior power `Ω^i_{X/S}` as a crystalline module sheaf on `Cris(X/S)`. -/
def crystallineOmegaPower
    {p : ℕ} [Fact (Nat.Prime p)]
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (i : ℕ) :
    CrisModuleSheaf S I γ h_compatible X x₀ where
  obj T := schemeModulesExteriorPower (Ω.module.obj T.obj.1) i
  comparison φ :=
    schemeModulesExteriorPowerComparison φ.hom.thickening (Ω.module.comparison φ.hom) i

/-- Evaluation of `Ω^i_{X/S}` on a small crystalline thickening. -/
theorem crystallineOmegaPower_obj
    {p : ℕ} [Fact (Nat.Prime p)]
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (i : ℕ) (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (crystallineOmegaPower Ω i).obj T =
      schemeModulesExteriorPower (Ω.module.obj T.obj.1) i :=
  sorry

/-- Tensor product of two crystalline module sheaves, formed objectwise over `𝒪_T`. -/
def crystallineTensor
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F G : CrisModuleSheaf S I γ h_compatible X x₀) :
    CrisModuleSheaf S I γ h_compatible X x₀ where
  obj T := schemeModulesTensor (F.obj T) (G.obj T)
  comparison φ :=
    schemeModulesTensorComparison φ.hom.thickening (F.comparison φ) (G.comparison φ)

/-- Evaluation of the objectwise tensor of crystalline module sheaves. -/
theorem crystallineTensor_obj
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F G : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (crystallineTensor F G).obj T = schemeModulesTensor (F.obj T) (G.obj T) :=
  sorry

/-- The coefficient sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` on `Cris(X/S)`. -/
def crystallineTensorOmegaPower
    {p : ℕ} [Fact (Nat.Prime p)]
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))}
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (i : ℕ) :
    CrisModuleSheaf S I γ h_compatible X x₀ :=
  crystallineTensor F (crystallineOmegaPower Ω i)

/-- Evaluation of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` on a small crystalline thickening. -/
theorem crystallineTensorOmegaPower_obj
    {p : ℕ} [Fact (Nat.Prime p)]
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))}
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (i : ℕ) (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (crystallineTensorOmegaPower F Ω i).obj T =
      schemeModulesTensor (F.obj T) ((crystallineOmegaPower Ω i).obj T) :=
  sorry

end
