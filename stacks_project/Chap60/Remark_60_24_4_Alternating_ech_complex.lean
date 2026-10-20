/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_PDDeRham
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_PDSquareZeroGeometry
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_PDFormsMap
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_SemilinearForms
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_StagePDConnection
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_ReindexedSemilinearLimit
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_CrossStageCoefficients
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_Bicomplex
public import stacks_project.Chap60.Remark_60_24_9_Base_change_isomorphism_BaseSections
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Tactic.CrossRefAttribute

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
variable (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
variable [SectionsCoherent I γS hc x₀ F]
variable [CrisModuleSheaf.IsCrystal F] [CrisModuleSheaf.IsLocallyQuasiCoherent F]
variable [LinearOrder c.Λ] [Fintype c.Λ]

/- Source 07MN refers to the final SHEAF of Cris(X/S), not a terminal
crystalline-site object. The latter need not exist: for A = F_p, I = 0,
X = affine line, the PD square-zero thickening has automorphism x ↦ x + ε.
A unique map to a terminal thickening would be invariant, but a local lift
of x changes by ε. Thus importing HasTerminal from older project statements
would exclude valid source examples.

moduleGlobalSectionsDerived derives toSheaf ⋙ Sheaf.Γ. On the actual crystal
placed in degree zero, its agreement with additive derived global sections
uses exact forgetting and Γ-acyclic underlying injective module sheaves
(Stacks 072Z, 0731), not preservation of injectives. Canonical universe lifting
on both sides preserves the coefficient and total-complex constructions. -/

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
noncomputable def totalDerived
    [HomologicalComplex₂.HasTotal (CrystallineSimplexPDComplex.bicomplex E hp hI hγ F)
      (ComplexShape.up ℕ)] : DerivedCategory AddCommGrpCat.{u + 1} :=
  DerivedCategory.Q.obj
    ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).obj
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (CrystallineSimplexPDComplex.total E hp hI hγ F)))

/-- Remark 60.24.4 (Alternating Čech complex): the ordered finite affine
cover and its polynomial presentations give completed coefficient/PD-form
tensor terms, signed Čech restrictions, and the crystal-induced de Rham
differential. Their total computes crystalline derived global sections.
The two derived objects are fixed by the geometry; no arbitrary comparison
or terminal crystalline-site object is supplied. -/
@[stacks 07MN]
theorem alternatingCech_computes
    [QuasiCompact x₀]
    [HasWeakSheafify (smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp)
      AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp)
      AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I γS hc x₀ p s hp))]
    [HomologicalComplex₂.HasTotal (CrystallineSimplexPDComplex.bicomplex E hp hI hγ F)
      (ComplexShape.up ℕ)] :
    IsIsomorphic (crystallineSections s hp F) (totalDerived E hp hI hγ F) := sorry

end CrystallineAlternatingComparison
