/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.PolynomialSite.QuillenSpectralSequence.LowDegree

/-!
# Low-degree terms of the Quillen spectral sequence

In the situation of Theorem 92.12.4, the first page contains the column-one cotangent terms,
the diagonal exterior-power terms, and off-diagonal symmetric-power homology terms. Its
horizontal differential supplies the two edge-map families and the low-degree five-term exact
sequence below.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Algebra
open CommAlgCat.Over.Polynomial.Site
open CategoryTheory.CategoryHomology
open CategoryTheory.HomologicalComplex.Filtered
open scoped DerivedTensorChangeOfRings DerivedTensorWithAlgebra ZeroObject

noncomputable section

universe u

/- Remark 92.12.5 -/
@[stacks 08RG] #check
  (Algebra.CotangentComplex.QuillenSpectralSequence.exists_lowDegreeFiveTerm_exact :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
      [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
      [HasProjectiveResolutions ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
      (hsurj : Function.Surjective (algebraMap A B)),
      ∃ (E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0)
        (F : FilteredComplex (ModuleCat.{u} B))
        (a : FilteredComplex.Association F E)
        (t : ∀ n : ℤ, F.underlying.homology n ≅
          Algebra.CotangentComplex.QuillenSpectralSequence.abutment A B n)
        (l : ∀ i : ℕ, 0 < i →
          ((F.gradedPiece 1).homology (-(i : ℤ)) ≅
            (Algebra.cotangentComplex A B).homology (-(i : ℤ))))
        (d : ∀ i : ℕ,
          (F.gradedPiece (i : ℤ)).homology (-(i : ℤ)) ≅
            (ModuleCat.of B
              (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent).exteriorPower i)
        (e : ∀ i : ℕ, 0 < i →
          (Algebra.CotangentComplex.QuillenSpectralSequence.abutment A B (-(i : ℤ)) ⟶
            (Algebra.cotangentComplex A B).homology (-(i : ℤ))))
        (g : ∀ i : ℕ,
          (ModuleCat.of B
            (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent).exteriorPower i ⟶
              Algebra.CotangentComplex.QuillenSpectralSequence.abutment A B (-(i : ℤ))),
        Algebra.CotangentComplex.QuillenSpectralSequence.IsQuillen A B E ∧
        CategoryTheory.FilteredComplex.Cohomology.Convergence.Converges F E ∧
        (∀ i : ℕ, (hi : 0 < i) →
          IsIso (Homology.map F 1 (-(i : ℤ))) ∧
          Homology.IsEdgeToGradedPiece F 1 (-(i : ℤ))
            ((t (-(i : ℤ))).hom ≫ e i hi ≫ (l i hi).inv)) ∧
        (∀ i : ℕ,
          IsIso (Homology.toGradedPiece F (i : ℤ) (-(i : ℤ))) ∧
          Homology.IsEdgeFromGradedPiece F (i : ℤ) (-(i : ℤ))
            ((d i).hom ≫ g i ≫ (t (-(i : ℤ))).inv)) ∧
        (ComposableArrows.mk₅
          (e 3 (by decide : (0 : ℕ) < 3))
          ((l 3 (by decide : (0 : ℕ) < 3)).inv ≫ TwoStep.boundary F 1
            (show (ComplexShape.up ℤ).Rel (-3) (-2) by norm_num) ≫ (d 2).hom)
          (g 2)
          (e 2 (by decide : (0 : ℕ) < 2))
          (0 : (Algebra.cotangentComplex A B).homology (-2) ⟶
            (0 : ModuleCat.{u} B))).Exact)

/- The full first-page formula retains the off-diagonal symmetric-power homology terms. -/
#check
  (Algebra.CotangentComplex.QuillenSpectralSequence.pageOne_eq :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
      [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
      [HasProjectiveResolutions ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
      (p : ℕ) (q : ℤ),
      Algebra.CotangentComplex.QuillenSpectralSequence.pageOne A B p q =
        if 0 ≤ -(p : ℤ) - q then
          moduleHomology (omegaSheaf A B ⋙ ModuleCat.symmetricPower.functor B p)
            (-(p : ℤ) - q).toNat
        else ModuleCat.of B PUnit)

/- Remark 92.12.5: polynomial-site homology computes cotangent homology. -/
@[stacks 08RG] #check
  (Algebra.CotangentComplex.polynomialSite_homology_isIsomorphic :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
      [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
      [HasProjectiveResolutions ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
      (n : ℕ),
      IsIsomorphic (moduleHomology (omegaSheaf A B) n)
        ((Algebra.cotangentComplex A B).homology (-n)))

/- Remark 92.12.5: the first polynomial-site homology is conormal. -/
@[stacks 08RG] #check
  (Algebra.CotangentComplex.QuillenSpectralSequence.omegaSheafHomology_one_isIsomorphic_conormal :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
      [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
      [HasProjectiveResolutions ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
      (hsurj : Function.Surjective (algebraMap A B)),
      IsIsomorphic (moduleHomology (omegaSheaf A B) 1)
        (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent))

/- Remark 92.12.5: diagonal symmetric-power homology is exterior power. -/
@[stacks 08RG] #check
  (Algebra.CotangentComplex.QuillenSpectralSequence.symmetricPower_homology_isIsomorphic_conormalExteriorPower :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
      [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
      [HasProjectiveResolutions ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
      (hsurj : Function.Surjective (algebraMap A B)) (k : ℕ),
      IsIsomorphic
        (moduleHomology (omegaSheaf A B ⋙ ModuleCat.symmetricPower.functor B k) k)
        ((ModuleCat.of B
          (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent).exteriorPower k))

/- Remark 92.12.5: degree-one Tor is conormal. -/
@[stacks 08RG] #check
  (Algebra.CotangentComplex.QuillenSpectralSequence.abutment_negOne_isIsomorphic_conormal :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
      [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
      [HasProjectiveResolutions ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
      (hsurj : Function.Surjective (algebraMap A B)),
      IsIsomorphic
        (Algebra.CotangentComplex.QuillenSpectralSequence.abutment A B (-1))
        (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent))

