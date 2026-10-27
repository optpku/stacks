/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower.Pullback
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Sections
public import ReasLib.AlgebraicGeometry.Crystalline.Differentials

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf
open PresheafOfModules

noncomputable section

universe u

/-- Comparison morphism for a tensor of module morphisms along a scheme morphism. -/
def schemeModulesTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} {M' N' : X.Modules}
    (gM : (pullback f).obj M ⟶ M') (gN : (pullback f).obj N ⟶ N') :
    (pullback f).obj (SheafOfModules.RingedSite.moduleTensor (𝒪 := Y.𝒪) M N) ⟶
      SheafOfModules.RingedSite.moduleTensor (𝒪 := X.𝒪) M' N' :=
  (RingedSpace.Hom.pullbackTensorIso f.toShHom M N).hom ≫
    SheafOfModules.RingedSite.moduleTensorMap (𝒪 := X.𝒪) gM gN

/-- Comparison morphism for an exterior power of a module morphism along a scheme morphism. -/
def schemeModulesExteriorPowerComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} {M' : X.Modules} (g : (pullback f).obj M ⟶ M') (i : ℕ) :
    (pullback f).obj (RingedSpace.ExteriorPower.sheaf M i) ⟶ RingedSpace.ExteriorPower.sheaf M' i :=
  RingedSpace.ExteriorPower.Pullback.comparison f.toShHom M i ≫
    SheafOfModules.RingedSite.ExteriorPower.map X.𝒪 g i

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
  obj T := RingedSpace.ExteriorPower.sheaf (Ω.module.obj T.obj.1) i
  comparison φ :=
    schemeModulesExteriorPowerComparison φ.hom.thickening (Ω.module.comparison φ.hom) i
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl
  comparison_id := sorry
  comparison_comp := sorry

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
      RingedSpace.ExteriorPower.sheaf (Ω.module.obj T.obj.1) i := rfl

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
  obj T := SheafOfModules.RingedSite.moduleTensor (𝒪 := T.obj.1.thickening.𝒪) (F.obj T) (G.obj T)
  comparison φ :=
    schemeModulesTensorComparison φ.hom.thickening (F.comparison φ) (G.comparison φ)
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl
  comparison_id := sorry
  comparison_comp := sorry

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
    (crystallineTensor F G).obj T =
      SheafOfModules.RingedSite.moduleTensor (𝒪 := T.obj.1.thickening.𝒪)
        (F.obj T) (G.obj T) := rfl

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
      SheafOfModules.RingedSite.moduleTensor (𝒪 := T.obj.1.thickening.𝒪)
        (F.obj T) ((crystallineOmegaPower Ω i).obj T) := rfl

namespace CrystallineModuleSheaf

variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- Sheafified tensor products preserve the intrinsic crystalline sheaf laws. -/
theorem crystallineTensor_isCrisSheaf (F G : CrisModuleSheaf S I γ h_compatible X x₀)
    (hF : IsCrisSheaf p s h_p F) (hG : IsCrisSheaf p s h_p G) :
    IsCrisSheaf p s h_p (crystallineTensor F G) := sorry

variable {h_I_quasiCoherent : I.toModule.IsQuasicoherent}

/-- Exterior powers of the genuine crystalline differential sheaf are genuine sheaves. -/
theorem crystallineOmegaPower_isCrisSheaf
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (i : ℕ) :
    IsCrisSheaf p s h_p (crystallineOmegaPower Ω i) := sorry

/-- The tensor coefficient is a genuine crystalline sheaf when its factors are genuine sheaves. -/
theorem crystallineTensorOmegaPower_isCrisSheaf
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (hF : IsCrisSheaf p s h_p F)
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (i : ℕ) :
    IsCrisSheaf p s h_p (crystallineTensorOmegaPower F Ω i) :=
  crystallineTensor_isCrisSheaf p s h_p F (crystallineOmegaPower Ω i) hF
    (crystallineOmegaPower_isCrisSheaf p s h_p Ω i)

/-- The actual abelian coefficient sheaf `F ⊗ Ω^i`, with sections computed by the
sheafified tensor and exterior-power constructions on each thickening. -/
def crystallineTensorOmegaPowerSheaf
    (F : CrisModuleSheaf S I γ h_compatible X x₀) (hF : IsCrisSheaf p s h_p F)
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (i : ℕ) :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u} :=
  IsCrisSheaf.abelianSheaf p s h_p
    (crystallineTensorOmegaPower_isCrisSheaf p s h_p F hF Ω i)

/-- The coefficient sheaf retains the global-section presheaf of the tensor assignment,
including all of its comparison-induced restriction maps. -/
theorem crystallineTensorOmegaPowerSheaf_obj
    (F : CrisModuleSheaf S I γ h_compatible X x₀) (hF : IsCrisSheaf p s h_p F)
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (i : ℕ) :
    (crystallineTensorOmegaPowerSheaf p s h_p F hF Ω i).obj =
      toAbelianPresheaf S I γ h_compatible X x₀ (crystallineTensorOmegaPower F Ω i) := rfl

end CrystallineModuleSheaf

end
