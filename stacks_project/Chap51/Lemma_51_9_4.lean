/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.Algebra.Homology.LocalCohomology
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.LocalCohomology

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
open scoped ENat

noncomputable section

universe u

variable (A M : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable [AddCommGroup M] [Module A M] [Module.Finite A M]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
variable (comparison :
  CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison (A := A))
variable (ω : DerivedCategory (ModuleCat.{u} A))
variable (hω : ω.IsNormalizedDualizingComplex comparison.closed)
variable (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
variable (hcanonical : ω.IsCanonicalNormalizedDualizingComplex C)
variable (i : ℤ) (n : ℕ) (p : PrimeSpectrum A)

/- Lemma 51.9.4 (1): finiteness of the negatively indexed Ext modules, expressed through the
canonical closed comparison. -/
@[stacks 0DWZ] #check (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.extModuleFinite A M comparison ω hω i :
    Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)).obj
        ((MonoidalClosed.ihomOf comparison.closed
          (ModuleCat.single0 (ModuleCat.of A M))).obj ω)))

/- Lemma 51.9.4 (2): the degree bounds use cohomological degree `-i`, so the canonical
 signed inequalities `-(d : ℤ) ≤ -i ≤ 0` are the source inequalities `0 ≤ i ≤ d`. -/
@[stacks 0DWZ] #check (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.extDegreeBounds A M C ω hcanonical (-i) :
    ¬ IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)).obj
        (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A)
          (ModuleCat.single0 (ModuleCat.of A M)) ω)) →
      ∃ d : ℕ, Module.supportDim A M = .some (d : ℕ∞) ∧
        -(d : ℤ) ≤ -i ∧ -i ≤ 0)

/- Lemma 51.9.4 (3): the support-dimension bound includes the zero-module bottom case and is
 written for the canonical signed cohomological degree `-i`. -/
@[stacks 0DWZ] #check (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.supportDim_ext_le A M C ω hcanonical (-i) :
    Module.supportDim A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)).obj
          (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A)
            (ModuleCat.single0 (ModuleCat.of A M)) ω)) = ⊥ ∨
      ∃ e : ℕ, Module.supportDim A
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)).obj
            (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A)
              (ModuleCat.single0 (ModuleCat.of A M)) ω)) =
        .some (e : ℕ∞) ∧ (e : ℤ) ≤ -(-i))

/- Lemma 51.9.4 (4): depth is the infimum of the nonzero negatively indexed Ext degrees. -/
@[stacks 0DWZ] #check (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.depth_eq_sInf_nonzero_extDegrees A M comparison.closed ω hω :
    moduleDepth A M =
      sInf {d : ℕ∞ | ∃ δ : ℕ, d = (δ : ℕ∞) ∧
        ¬ IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(δ : ℤ))).obj
            ((MonoidalClosed.ihomOf comparison.closed
              (ModuleCat.single0 (ModuleCat.of A M))).obj ω))})

/- Lemma 51.9.4 (5): localized depth detects membership in the support of the initial Ext
degrees. -/
@[stacks 0DWZ] #check (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.mem_support_extUpTo_iff A M comparison ω hω n p :
    (∃ j : ℕ, j ≤ n ∧
      p ∈ Module.support A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(j : ℤ))).obj
          ((MonoidalClosed.ihomOf comparison.closed
            (ModuleCat.single0 (ModuleCat.of A M))).obj ω))) ↔
      (.some (moduleDepth (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)) : WithBot ℕ∞) +
          ringKrullDim (A ⧸ p.asIdeal) ≤ .some (n : ℕ∞))

/- Lemma 51.9.4 (6): the annihilator of each Ext module equals that of the corresponding local
cohomology module. -/
@[stacks 0DWZ] #check (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.annihilator_ext_eq_localCohomology A M comparison ω hω n :
    Module.annihilator A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
        ((MonoidalClosed.ihomOf comparison.closed
          (ModuleCat.single0 (ModuleCat.of A M))).obj ω)) =
      Module.annihilator A
        ((localCohomology (IsLocalRing.maximalIdeal A) n).obj (ModuleCat.of A M)))
