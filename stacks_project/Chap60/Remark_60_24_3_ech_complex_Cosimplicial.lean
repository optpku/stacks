/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cech.Cosimplicial

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf CechCrisCover

universe u



variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} {γA : DividedPowers IA}
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
      (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
        ((Spec (.of A)).presheaf.map
          (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
variable {c : CechCrisCover x₀}

/-- The affine ideal sheaf agrees with the ideal associated to the specified ring ideal. -/
abbrev specIdealEqOfIdealTop (IA : Ideal A) (I : (Spec.{u} (.of A)).IdealSheafData) : Prop :=
  Affine.idealCompatible IA I

/-- Global divided powers agree with the specified affine ring divided powers. -/
abbrev specDividedPowersEq (IA : Ideal A) (γA : DividedPowers IA)
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)) : Prop :=
  Affine.dividedPowersCompatible IA γA I γS

variable (E : CechCrisEnvelope p IA γA c)

/- The completed simplex products form the divided-power cosimplicial ring. -/
#check (CechCrisEnvelope.cechDPCosimplicial E : CosimplicialObject DividedPowerRing.{u})

variable (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
variable (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀)

/- The coefficient products retain their canonical associated cochain complex. -/
#check (CechCrisEnvelope.cechCrisComplex E s h_p hI hγ F :
  CochainComplex AddCommGrpCat.{u} ℕ)

end
