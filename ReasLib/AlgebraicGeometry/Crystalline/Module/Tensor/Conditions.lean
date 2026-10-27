/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Module.Tensor
public import ReasLib.AlgebraicGeometry.Crystalline.Affine

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf

universe u

variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)

/-- Every exterior power of the universal crystalline differentials is locally
quasi-coherent. -/
theorem crystallineOmegaPower_isLocallyQuasiCoherent (i : ℕ) :
    ModuleSheaf.IsLocallyQuasiCoherent (crystallineOmegaPower Ω i) := sorry

/-- Every exterior power of the universal crystalline differentials has
epimorphic comparisons along closed immersions of thickenings. -/
theorem crystallineOmegaPower_comparison_epi_of_closedImmersion (i : ℕ) :
    comparison_epi_of_closedImmersion S I γ h_compatible X x₀
      (crystallineOmegaPower Ω i) := sorry
