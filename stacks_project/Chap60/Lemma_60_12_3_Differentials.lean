/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Differentials

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf
open scoped AlgebraicGeometry RelativeDerivation

universe u v w

#check (CrystallineDifferentials.of : ∀ (p : ℕ) [Fact (Nat.Prime p)]
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
    (module : CrystallineModuleSheaf S I γ h_compatible X x₀)
    (derivation : CrystallineModuleSheaf.SDerivation p S I γ h_compatible s X x₀ h_p module)
    (comparison : ∀ (T : CRIS S I γ h_compatible X x₀)
      (h_quasiCoherent : T.ideal.toModule.IsQuasicoherent)
      (D : DividedPowerScheme.RelativeDifferentials
        (CrystallineObject.toDividedPowerScheme T h_quasiCoherent)
        S T.thickeningToBase),
      module.obj T ⟶ D.module)
    (comparison_derivation : ∀ (T : CRIS S I γ h_compatible X x₀)
    (h_quasiCoherent : T.ideal.toModule.IsQuasicoherent)
    (D : DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T h_quasiCoherent) S T.thickeningToBase),
    (derivation.component T).postcomp (comparison T h_quasiCoherent D).val =
      (d[T.thickeningToBase.toShHom]).postcomp D.quotient.val)
    (universal : ∀ (F : CrystallineModuleSheaf S I γ h_compatible X x₀)
      (D : CrystallineModuleSheaf.SDerivation p S I γ h_compatible s X x₀ h_p F),
      ∃! q : CrystallineModuleMap S I γ h_compatible X x₀ module F,
        ∀ (T : CRIS S I γ h_compatible X x₀),
          (derivation.component T).postcomp (q.component T).val = D.component T),
    CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)

