/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Crystalline.Cech.Alternating
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.BaseSections
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CrystallineModuleSheaf CrystallineCoefficients CechCrisCover
open AlgebraicGeometry.Scheme.Crystalline
universe u
namespace CrystallineAlternatingComparison

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} {γA : DividedPowers IA}
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)}
variable {hc : ∀ (V : (Spec.{u} (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme} {c : CechCrisCover x₀}
variable (E : CechCrisEnvelope p IA γA c)
variable (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (hp : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (hI : Affine.idealCompatible IA I) (hγ : Affine.dividedPowersCompatible IA γA I γS)
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
variable [SectionsCoherent I γS hc x₀ F]
variable [CrisModuleSheaf.IsCrystal F] [CrisModuleSheaf.IsLocallyQuasiCoherent F]
variable [LinearOrder c.Λ] [Fintype c.Λ]

/-- Genuine derived global sections of the coherent crystal coefficient
sheaf. Global sections mean the sheaf functor Γ, not evaluation at a terminal
object of the crystalline site. -/
noncomputable def crystallineSections
    [HasWeakSheafify (smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp)
      AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp)
      AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I γS hc x₀ p s hp))] :
    DerivedCategory AddCommGrpCat.{u + 1} :=
  (RingedSite.Hom.moduleGlobalSectionsDerived.{u + 1}
    (liftedRingedSite I γS hc x₀ p s hp)).obj
      (derivedOfCrystal I γS hc x₀ p s hp F)

/-- The actual ordered total complex is lifted only in universe size and
extended from nonnegative cochain degrees before localization. -/
noncomputable def totalDerived : DerivedCategory AddCommGrpCat.{u + 1} :=
  DerivedCategory.Q.obj
    ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).obj
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (CrystallineSimplexPDComplex.total E hp hI hγ F)))

/-- The ordered completed Čech–de Rham total of a finite affine cover computes crystalline derived global sections. -/
theorem alternatingCech_computes
    [HasWeakSheafify (smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp)
      AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp)
      AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I γS hc x₀ p s hp))] :
    IsIsomorphic (crystallineSections s hp F) (totalDerived E hp hI hγ F) := sorry

end CrystallineAlternatingComparison
