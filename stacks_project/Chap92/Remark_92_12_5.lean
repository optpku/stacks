module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap92.Lemma_92_11_2
public import stacks_project.Chap92.Remark_92_12_2
public import stacks_project.Chap92.Theorem_92_12_4_Quillen_spectral_sequence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Low-degree terms of the Quillen spectral sequence

In the situation of Theorem 92.12.4, with `I = Ker(A → B)`, the first page of a
Quillen spectral sequence is concentrated on the `p = 1` column
`H^{-i}(L_{B/A})` and the diagonal `∧^i_B(I/I²)`, with horizontal `d₁`. This
yields the identifications `H^{-1}(L_{B/A}) ≅ H_1(C_{B/A}, Ω) ≅ I/I²` and
`H_k(C_{B/A}, Sym^k(Ω)) ≅ ∧^k_B(I/I²)`, the equality `Tor_1^A(B, B) = I/I²`,
and the five-term exact sequence of low degree terms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Algebra
open CommAlgCat.Over.Polynomial.Site
open CategoryTheory.CategoryHomology
open scoped DerivedTensorChangeOfRings DerivedTensorWithAlgebra ZeroObject

noncomputable section

universe u

namespace Algebra.CotangentComplex.QuillenSpectralSequence

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasProjectiveResolutions ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]

/-- Remark 92.12.5 (1). In the situation of Theorem 92.12.4, with `I = Ker(A → B)`,
one has `H^{-1}(L_{B/A}) = H_1(C_{B/A}, Ω)`. -/
@[stacks 08RG]
theorem cotangentHomology_negOne_isIsomorphic_omegaSheafHomology
    (hsurj : Function.Surjective (algebraMap A B)) :
    IsIsomorphic ((Algebra.cotangentComplex A B).homology (-1))
      (moduleHomology (omegaSheaf A B) 1) :=
  sorry

/-- Remark 92.12.5 (2). In the situation of Theorem 92.12.4, with `I = Ker(A → B)`,
one has `H_1(C_{B/A}, Ω) = I/I²`. -/
@[stacks 08RG]
theorem omegaSheafHomology_one_isIsomorphic_conormal
    (hsurj : Function.Surjective (algebraMap A B)) :
    IsIsomorphic (moduleHomology (omegaSheaf A B) 1)
      (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent) :=
  sorry

/-- Remark 92.12.5 (3). In the situation of Theorem 92.12.4, with `I = Ker(A → B)`,
`H_k(C_{B/A}, Sym^k(Ω)) = ∧^k_B(I/I²)` by Remark 92.12.2. This is the diagonal
`E₁` term `pageOne k (-(2 * k))`. The differential `d₁` is horizontal because a
Quillen spectral sequence is a `CohomologicalSpectralSequence`, and the
identifications `E₁^{1, -1 - i} ≅ H^{-i}(L_{B/A})` and
`E₁^{i, -2 * i} ≅ ∧^i_B(I/I²)` produce the source edge maps
`Tor_i^A(B, B) ⟶ H^{-i}(L_{B/A})` for `i > 0` and
`∧^i_B(I/I²) ⟶ Tor_i^A(B, B)`. -/
@[stacks 08RG]
theorem symmetricPower_homology_isIsomorphic_conormalExteriorPower
    (hsurj : Function.Surjective (algebraMap A B)) (k : ℕ) :
    IsIsomorphic
      (moduleHomology (omegaSheaf A B ⋙ ModuleCat.symmetricPower.functor B k) k)
      ((ModuleCat.of B
          (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent).exteriorPower k) :=
  sorry

/-- Remark 92.12.5 (4). In the situation of Theorem 92.12.4, with `I = Ker(A → B)`,
`Tor_1^A(B, B) = I/I²` as objects of `ModuleCat B`. -/
@[stacks 08RG]
theorem abutment_negOne_isIsomorphic_conormal
    (hsurj : Function.Surjective (algebraMap A B)) :
    IsIsomorphic (abutment A B (-1))
      (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent) :=
  sorry

/-- Remark 92.12.5 (5). In the situation of Theorem 92.12.4, with `I = Ker(A → B)`,
the `E₁`-page identifications `E₁^{1, -1 - i} ≅ H^{-i}(L_{B/A})` and
`E₁^{i, -2 * i} ≅ ∧^i_B(I/I²)`, together with the horizontal differential `d₁`
of a `CohomologicalSpectralSequence`, yield a five-term exact sequence of low
degree terms
`Tor_3^A(B, B) ⟶ H^{-3}(L_{B/A}) ⟶ ∧^2_B(I/I²) ⟶ Tor_2^A(B, B) ⟶
H^{-2}(L_{B/A}) ⟶ 0`. -/
@[stacks 08RG]
theorem exists_lowDegreeFiveTerm_exact
    (hsurj : Function.Surjective (algebraMap A B)) :
    ∃ (α : abutment A B (-3) ⟶ (Algebra.cotangentComplex A B).homology (-3))
      (β : (Algebra.cotangentComplex A B).homology (-3) ⟶
        (ModuleCat.of B
            (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent).exteriorPower 2)
      (γ : (ModuleCat.of B
            (Extension.ofSurjective (Algebra.ofId A B) hsurj).Cotangent).exteriorPower 2 ⟶
        abutment A B (-2))
      (δ : abutment A B (-2) ⟶ (Algebra.cotangentComplex A B).homology (-2)),
      (ComposableArrows.mk₅ α β γ δ
        (0 : (Algebra.cotangentComplex A B).homology (-2) ⟶
          (0 : ModuleCat.{u} B))).Exact :=
  sorry

/-- Category homology of `omegaSheaf` in degree `n` is isomorphic to
`H^{-n}(L_{B/A})`. -/
theorem omegaSheafHomology_isIsomorphic_cotangentHomology (n : ℕ) :
    IsIsomorphic (moduleHomology (omegaSheaf A B) n)
      ((Algebra.cotangentComplex A B).homology (-n)) :=
  sorry

end Algebra.CotangentComplex.QuillenSpectralSequence
