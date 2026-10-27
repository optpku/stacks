/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Module.Underlined
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Sections
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

namespace CrystallineModuleSheaf.CrisModuleSheaf

/-- The underlined module of a quasi-coherent source module has epimorphic
comparisons along closed immersions of crystalline thickenings. -/
theorem underlined_comparison_epi_of_closedImmersion
    (M : X.Modules) [M.IsQuasicoherent] :
    comparison_epi_of_closedImmersion S I γ h_compatible X x₀
      (underlined I γ h_compatible x₀ M) := sorry

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- The underlined module of any source module satisfies crystalline restriction
compatibility and Zariski descent. -/
theorem underlined_isCrisSheaf (M : X.Modules) :
    IsCrisSheaf p s h_p (underlined I γ h_compatible x₀ M) := sorry

end CrystallineModuleSheaf.CrisModuleSheaf
