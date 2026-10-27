/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cech.Cover.Affine
public import ReasLib.AlgebraicGeometry.Crystalline.Cech.Comparison
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf CechCrisCover CechCrisEnvelope
open DividedPowers.PAdic

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.Affine

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type u} [CommRing C] [Algebra A C]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
      (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
        ((Spec (.of A)).presheaf.map
          (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom}
variable (x₀ : Spec.{u} (.of C) ⟶ I.subscheme)
variable (hx₀ : structureMapCompatible I x₀)
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
variable (E : CechCrisEnvelope p IA γA (CechCrisCover.ofAffine x₀ hx₀ π hπ))
variable (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : (Spec.{u} (.of C)).affineOpens,
  IsNilpotent (p : Γ(Spec (.of C), U)))
variable (hI : idealCompatible IA I) (hγ : dividedPowersCompatible IA γA I γS)

/-- Each term of the affine polynomial-envelope Čech complex is isomorphic to
the inverse-limit sections on the completed envelope of its unique simplex. -/
theorem sectionsComplex_obj
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀) (n : ℕ) :
    IsIsomorphic ((E.cechCrisComplex s h_p hI hγ F).X n)
      ((CechCrisCover.ofAffine x₀ hx₀ π hπ).simplexModule hI hγ F n
        (fun _ => PUnit.unit) s h_p
        (E.hIJ n (fun _ => PUnit.unit)) (E.E n (fun _ => PUnit.unit))
        (E.hE n (fun _ => PUnit.unit)) (E.N n (fun _ => PUnit.unit))
        (E.hN n (fun _ => PUnit.unit)) (E.γhat n (fun _ => PUnit.unit))
        (envelopeCompletionDividedPowers_isDPMorphism
          (E.E n (fun _ => PUnit.unit)) (E.N n (fun _ => PUnit.unit))
          (E.hN n (fun _ => PUnit.unit)))) := sorry

/-- For a locally quasi-coherent crystalline module sheaf with epimorphic
closed-immersion comparisons, the affine polynomial-envelope Čech complex
computes derived global sections. -/
theorem sectionsComplex_computes
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
    [ModuleSheaf.IsLocallyQuasiCoherent F]
    (hF : IsCrisSheaf p s h_p F)
    (h_epi : comparison_epi_of_closedImmersion
      (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀ F) :
    IsIsomorphic
      (CrystallineModuleSheaf.derivedGlobalSections p (Spec (.of A)) I γS h_compatible s
        (Spec (.of C)) x₀ h_p F)
      ((DerivedCategory.Q).obj
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).obj
          ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (E.cechCrisComplex s h_p hI hγ F)))) := sorry

/-- Crystalline cohomology of a locally quasi-coherent module sheaf with
epimorphic closed-immersion comparisons is the homology of the universe-raised
affine polynomial-envelope Čech complex. -/
theorem sectionsComplex_cohomology
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
    [ModuleSheaf.IsLocallyQuasiCoherent F]
    (hF : IsCrisSheaf p s h_p F)
    (h_epi : comparison_epi_of_closedImmersion
      (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀ F) (n : ℕ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (n : ℤ)).obj
        (CrystallineModuleSheaf.derivedGlobalSections p (Spec (.of A)) I γS h_compatible s
          (Spec (.of C)) x₀ h_p F))
      (((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (E.cechCrisComplex s h_p hI hγ F)).homology n) := sorry

end AlgebraicGeometry.Scheme.Crystalline.Affine
