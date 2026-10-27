/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Module.Tensor

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf

@[expose] public section

universe u w

variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- The canonical comparison of `Ω_{X/S}` with `Ω_{T/S, δ}` on `T`. -/
def crystallineDifferentialsIdent
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (h_T_quasiCoherent : T.obj.1.ideal.toModule.IsQuasicoherent)
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (D_T : DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T.obj.1 h_T_quasiCoherent)
      S T.obj.1.thickeningToBase) :
    Ω_XS.module.obj T.obj.1 ⟶ D_T.module :=
  Ω_XS.comparison T.obj.1 h_T_quasiCoherent D_T

/-- The differentials identification is the universal differential comparison. -/
theorem crystallineDifferentialsIdent_eq
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (h_T_quasiCoherent : T.obj.1.ideal.toModule.IsQuasicoherent)
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (D_T : DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T.obj.1 h_T_quasiCoherent)
      S T.obj.1.thickeningToBase) :
    crystallineDifferentialsIdent p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p T
      h_T_quasiCoherent Ω_XS D_T =
      Ω_XS.comparison T.obj.1 h_T_quasiCoherent D_T := rfl

/-- Objectwise tensor of a small crystalline module sheaf with the restriction of
`Ω_{X/S}` to `Cris(X / S)`. This single-module construction is superseded by
the full divided-power de Rham complex for derived cohomology. -/
noncomputable def crystallineDeRham
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    {p : ℕ} [Fact (Nat.Prime p)]
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
    {h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))}
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p) :
    CrisModuleSheaf S I γ h_compatible X x₀ :=
  crystallineTensor F (restrictCrystallineModule Ω_XS.module)

/-- The crystalline de Rham sheaf evaluates to `F.obj T ⊗ Ω_{X/S}|_T`. -/
theorem crystallineDeRham_obj
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    {p : ℕ} [Fact (Nat.Prime p)]
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
    {h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))}
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (crystallineDeRham F Ω_XS).obj T =
      SheafOfModules.RingedSite.moduleTensor (𝒪 := T.obj.1.thickening.𝒪)
        (F.obj T) (Ω_XS.module.obj T.obj.1) := rfl

/-- Restriction of derived global sections of a sheaf on `Cris(X / S)` to the object `T`,
obtained by applying a global-sections restriction natural transformation to evaluation
at `T` followed by `RΓ(T, -)`. This supplied-transformation construction is
superseded by canonical restriction on the derived categories of abelian sheaves. -/
noncomputable def crystallineRestrictToT
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {D : Type w} [Category.{w} D]
    (rGammaCris : CrisModuleSheaf S I γ h_compatible X x₀ ⥤ D)
    (rGammaT : (T.obj.1.thickening).Modules ⥤ D)
    (restrictToT : rGammaCris ⟶ crystallineEvalFunctor T ⋙ rGammaT)
    (G : CrisModuleSheaf S I γ h_compatible X x₀) :
    rGammaCris.obj G ⟶ rGammaT.obj (G.obj T) :=
  restrictToT.app G

/-- Restriction to `T` is the component of the evaluation natural transformation. -/
theorem crystallineRestrictToT_eq
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {D : Type w} [Category.{w} D]
    (rGammaCris : CrisModuleSheaf S I γ h_compatible X x₀ ⥤ D)
    (rGammaT : (T.obj.1.thickening).Modules ⥤ D)
    (restrictToT : rGammaCris ⟶ crystallineEvalFunctor T ⋙ rGammaT)
    (G : CrisModuleSheaf S I γ h_compatible X x₀) :
    crystallineRestrictToT T rGammaCris rGammaT restrictToT G = restrictToT.app G := rfl

/-- Tensor the universal differential comparison with `F.obj T` and apply `RΓ(T, -)`. -/
noncomputable def crystallineRestriction_differentialsIdent
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [F.IsCrystal] [F.IsLocallyQuasiCoherent]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (h_T_quasiCoherent : T.obj.1.ideal.toModule.IsQuasicoherent)
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (D_T : DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T.obj.1 h_T_quasiCoherent)
      S T.obj.1.thickeningToBase)
    {D : Type w} [Category.{w} D]
    (rGammaT : (T.obj.1.thickening).Modules ⥤ D) :
    rGammaT.obj (SheafOfModules.RingedSite.moduleTensor (𝒪 := T.obj.1.thickening.𝒪)
      (crystallineEval F T) (Ω_XS.module.obj T.obj.1)) ⟶
      rGammaT.obj (SheafOfModules.RingedSite.moduleTensor (𝒪 := T.obj.1.thickening.𝒪)
        (crystallineEval F T) D_T.module) :=
  rGammaT.map
    (SheafOfModules.RingedSite.moduleTensorMap (𝒪 := T.obj.1.thickening.𝒪) (𝟙 (crystallineEval F T))
      (crystallineDifferentialsIdent p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p T
        h_T_quasiCoherent Ω_XS D_T))

/-- The crystalline restriction morphism composes the supplied de Rham transformation,
restriction to a thickening, and the universal differential comparison. This
single-module composite is superseded by canonical restriction to the full
divided-power de Rham complex for derived cohomology. -/
noncomputable def crystallineRestriction
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [F.IsCrystal] [F.IsLocallyQuasiCoherent]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (h_T_quasiCoherent : T.obj.1.ideal.toModule.IsQuasicoherent)
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (D_T : DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T.obj.1 h_T_quasiCoherent)
      S T.obj.1.thickeningToBase)
    {D : Type w} [Category.{w} D]
    (rGammaCris : CrisModuleSheaf S I γ h_compatible X x₀ ⥤ D)
    (rGammaT : (T.obj.1.thickening).Modules ⥤ D)
    (deRhamIdent :
      rGammaCris.obj F ⟶ rGammaCris.obj (crystallineDeRham F Ω_XS))
    (restrictToT : rGammaCris ⟶ crystallineEvalFunctor T ⋙ rGammaT) :
    rGammaCris.obj F ⟶
      rGammaT.obj (SheafOfModules.RingedSite.moduleTensor (𝒪 := T.obj.1.thickening.𝒪)
        (crystallineEval F T) D_T.module) :=
  deRhamIdent ≫
    crystallineRestrictToT T rGammaCris rGammaT restrictToT (crystallineDeRham F Ω_XS) ≫
      crystallineRestriction_differentialsIdent p S I γ h_compatible
        h_I_quasiCoherent s X x₀ h_p F T h_T_quasiCoherent Ω_XS D_T rGammaT

/-- The crystalline restriction morphism is the de Rham identification of
the de Rham comparison, restriction of global classes to `T`, and the
universal differential identification of `Ω_{X/S}` with `Ω_{T/S, δ}` tensored with `F.obj T`. -/
theorem crystallineRestriction_spec
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [F.IsCrystal] [F.IsLocallyQuasiCoherent]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (h_T_quasiCoherent : T.obj.1.ideal.toModule.IsQuasicoherent)
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (D_T : DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T.obj.1 h_T_quasiCoherent)
      S T.obj.1.thickeningToBase)
    {D : Type w} [Category.{w} D]
    (rGammaCris : CrisModuleSheaf S I γ h_compatible X x₀ ⥤ D)
    (rGammaT : (T.obj.1.thickening).Modules ⥤ D)
    (deRhamIdent :
      rGammaCris.obj F ⟶ rGammaCris.obj (crystallineDeRham F Ω_XS))
    (restrictToT : rGammaCris ⟶ crystallineEvalFunctor T ⋙ rGammaT) :
    crystallineRestriction p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p F T
      h_T_quasiCoherent Ω_XS D_T rGammaCris rGammaT deRhamIdent restrictToT =
      deRhamIdent ≫
        crystallineRestrictToT T rGammaCris rGammaT restrictToT
          (crystallineDeRham F Ω_XS) ≫
          rGammaT.map
            (SheafOfModules.RingedSite.moduleTensorMap (𝒪 := T.obj.1.thickening.𝒪) (𝟙 (crystallineEval F T))
              (crystallineDifferentialsIdent p S I γ h_compatible h_I_quasiCoherent
                s X x₀ h_p T h_T_quasiCoherent Ω_XS D_T)) := rfl
