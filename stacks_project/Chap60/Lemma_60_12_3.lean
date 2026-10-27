/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Differentials

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf
open scoped AlgebraicGeometry RelativeDerivation

universe u v w

/- Lemma 60.12.3 (1) -/
@[stacks 07IZ]
#check (CrystallineDifferentials.comparison_isIso : ∀ (p : ℕ) [Fact (Nat.Prime p)]
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
      S T.obj.1.thickeningToBase),
    IsIso (Ω_XS.comparison T.obj.1 h_T_quasiCoherent D_T))

/- Lemma 60.12.3 (2) -/
@[stacks 07IZ]
#check (CrystallineDifferentials.comparison_spec : ∀ (p : ℕ) [Fact (Nat.Prime p)]
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
      S T.obj.1.thickeningToBase),
    (Ω_XS.derivation.component T.obj.1).postcomp
        (Ω_XS.comparison T.obj.1 h_T_quasiCoherent D_T).val =
      (d[T.obj.1.thickeningToBase.toShHom]).postcomp D_T.quotient.val)

