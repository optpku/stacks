/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Module.Coefficients

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf CrystallineCoefficients

universe u

variable {S X : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : S.affineOpens) (f : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
    (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (x₀ : X ⟶ I.subscheme)

variable (F : CrisModuleSheaf S I γ hc X x₀)
variable (p : ℕ) [Fact p.Prime]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (hp : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable [CrisModuleSheaf.IsCrystal F]

/- Crystalline coefficient realization is provided by its shared mathematical owner. -/
#check (CrystallineCoefficients.liftedOfCrystal I γ hc x₀ F p s hp :
  SheafOfModules.{u + 1} (CrystallineCoefficients.liftedStructureSheaf I γ hc x₀ p s hp))
