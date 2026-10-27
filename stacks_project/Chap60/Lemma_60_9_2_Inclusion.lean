/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Inclusion

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline

universe u

variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/- The raw-parameter crystalline API remains available through its mathematical owner. -/
#check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineInclusion
  S I γ h_compatible X x₀ :
  smallCrystallineSite S I γ h_compatible X x₀ ⥤
    RelativeCRIS S I γ h_compatible X x₀)

#check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineInclusion_preservesFiniteNonemptyLimits
  S I γ h_compatible X x₀ :
  PreservesFiniteNonemptyLimits
    (smallCrystallineInclusion S I γ h_compatible X x₀))

#check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineInclusion_fullyFaithful
  S I γ h_compatible X x₀ :
  (smallCrystallineInclusion S I γ h_compatible X x₀).FullyFaithful)

#check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineInclusion_isContinuous
  S I γ h_compatible X x₀ p s h_p :
  Functor.IsContinuous (smallCrystallineInclusion S I γ h_compatible X x₀)
    (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    (crystallineZariskiTopology S I γ h_compatible X x₀))

#check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineInclusion_isCocontinuous
  S I γ h_compatible X x₀ p s h_p :
  Functor.IsCocontinuous (smallCrystallineInclusion S I γ h_compatible X x₀)
    (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    (crystallineZariskiTopology S I γ h_compatible X x₀))

#check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineSite_hasFiniteNonemptyLimits
  S I γ h_compatible X x₀ :
  HasFiniteNonemptyLimits (smallCrystallineSite S I γ h_compatible X x₀))
