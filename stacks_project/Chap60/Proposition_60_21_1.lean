/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Affine
public import ReasLib.AlgebraicGeometry.Crystalline.Affine.PolynomialCohomology
public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Site
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf

universe u

export AlgebraicGeometry.Scheme.Crystalline (comparison_epi_of_closedImmersion)

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C] [Algebra A C]

/-- Compatibility spelling for the ideal sheaf on `Spec A` associated with `IA`. -/
abbrev specIdealEqOfIdealTop (IA : Ideal A) (I : (Spec.{u} (.of A)).IdealSheafData) : Prop :=
  Affine.idealCompatible IA I

/-- Compatibility spelling for divided powers transported along `ΓSpecIso`. -/
abbrev specDividedPowersEq (IA : Ideal A) (γA : DividedPowers IA)
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)) : Prop :=
  Affine.dividedPowersCompatible IA γA I γS

/-- Compatibility spelling for the structure map induced by `algebraMap A C`. -/
abbrev IsCanonicalCrisStructureMap
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (x₀ : Spec.{u} (.of C) ⟶ I.subscheme) : Prop :=
  Affine.structureMapCompatible I x₀

/- Proposition 60.21.1: for the affine crystalline setup, a locally quasi-coherent
crystalline module sheaf with surjective closed-immersion comparisons has derived
global sections computed by the polynomial-envelope complex `M(0) → M(1) → ⋯`. -/
@[stacks 07JN] #check
  (AlgebraicGeometry.Scheme.Crystalline.Affine.sectionsComplex_computes :
    ∀ {p : ℕ} [Fact (Nat.Prime p)] {A : Type u} [CommRing A]
      [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
      {C : Type u} [CommRing C] [Algebra A C]
      {IA : Ideal A} (γA : DividedPowers IA)
      {I : (Spec.{u} (.of A)).IdealSheafData}
      {γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)}
      {h_compatible :
        ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
          (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
            ((Spec (.of A)).presheaf.map
              (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom}
      (x₀ : Spec.{u} (.of C) ⟶ I.subscheme)
      (hx₀ : Affine.structureMapCompatible I x₀)
      {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
      (E : CechCrisEnvelope p IA γA (CechCrisCover.ofAffine x₀ hx₀ π hπ))
      (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
      (h_p : ∀ U : (Spec.{u} (.of C)).affineOpens,
        IsNilpotent (p : Γ(Spec (.of C), U)))
      (hI : Affine.idealCompatible IA I) (hγ : Affine.dividedPowersCompatible IA γA I γS)
      (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
      [ModuleSheaf.IsLocallyQuasiCoherent F]
      (hF : IsCrisSheaf p s h_p F)
      (h_epi : AlgebraicGeometry.Scheme.Crystalline.comparison_epi_of_closedImmersion
        (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀ F),
      IsIsomorphic
        (CrystallineModuleSheaf.derivedGlobalSections p (Spec (.of A)) I γS h_compatible s
          (Spec (.of C)) x₀ h_p F)
        ((DerivedCategory.Q).obj
          ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).obj
            ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
              (ComplexShape.up ℕ)).obj (E.cechCrisComplex s h_p hI hγ F)))))

