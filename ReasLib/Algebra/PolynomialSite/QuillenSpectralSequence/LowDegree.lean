/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite.QuillenSpectralSequence
public import ReasLib.RingTheory.CotangentComplex.PolynomialSite.Homology
public import ReasLib.RingTheory.CotangentComplex.Surjective
public import ReasLib.CategoryTheory.Sites.CategoryHomology.SymmetricPower
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.EdgeMaps
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence

/-!
# Low-degree terms of the Quillen spectral sequence

For a surjective commutative algebra map, the polynomial-site comparison, conormal and diagonal
identifications, and the edge maps in low degree form the standard five-term exact sequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.HomologicalComplex.Filtered
open Algebra
open CommAlgCat.Over.Polynomial.Site
open CategoryTheory.CategoryHomology
open CategoryTheory.FilteredComplex.Cohomology.Convergence
open scoped DerivedTensorChangeOfRings DerivedTensorWithAlgebra ZeroObject

noncomputable section

universe u

namespace Algebra.CotangentComplex.QuillenSpectralSequence

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasProjectiveResolutions ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]

/-- The first polynomial-site homology object is the conormal module for a surjection. -/
theorem omegaSheafHomology_one_isIsomorphic_conormal
    (hsurj : Function.Surjective (algebraMap A B)) :
    IsIsomorphic (moduleHomology (omegaSheaf A B) 1)
      (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent) :=
  sorry

/-- The degree-`k` diagonal polynomial-site homology object is the exterior power of the
conormal module. -/
theorem symmetricPower_homology_isIsomorphic_conormalExteriorPower
    (hsurj : Function.Surjective (algebraMap A B)) (k : ℕ) :
    IsIsomorphic
      (moduleHomology (omegaSheaf A B ⋙ ModuleCat.symmetricPower.functor B k) k)
      ((ModuleCat.of B
          (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent).exteriorPower k) :=
  sorry

/-- A surjective algebra map admits an associated convergent filtered model whose two edge-map
families and transported graded boundary form the low-degree five-term exact sequence. -/
theorem exists_lowDegreeFiveTerm_exact
    (hsurj : Function.Surjective (algebraMap A B)) :
    ∃ (E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0)
      (F : FilteredComplex (ModuleCat.{u} B))
      (a : FilteredComplex.Association F E)
      (t : ∀ n : ℤ, F.underlying.homology n ≅ abutment A B n)
      (l : ∀ i : ℕ, 0 < i →
        ((F.gradedPiece 1).homology (-(i : ℤ)) ≅
          (Algebra.cotangentComplex A B).homology (-(i : ℤ))))
      (d : ∀ i : ℕ,
        (F.gradedPiece (i : ℤ)).homology (-(i : ℤ)) ≅
          (ModuleCat.of B
            (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent).exteriorPower i)
      (e : ∀ i : ℕ, 0 < i →
        (abutment A B (-(i : ℤ)) ⟶
          (Algebra.cotangentComplex A B).homology (-(i : ℤ))))
      (g : ∀ i : ℕ,
        (ModuleCat.of B
          (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent).exteriorPower i ⟶
            abutment A B (-(i : ℤ))),
      IsQuillen A B E ∧
      Converges F E ∧
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
          (0 : ModuleCat.{u} B))).Exact :=
  sorry

/-- The degree-one Tor abutment is the conormal module for a surjective algebra map. -/
theorem abutment_negOne_isIsomorphic_conormal
    (hsurj : Function.Surjective (algebraMap A B)) :
    IsIsomorphic (abutment A B (-1))
      (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent) :=
  sorry

end Algebra.CotangentComplex.QuillenSpectralSequence
