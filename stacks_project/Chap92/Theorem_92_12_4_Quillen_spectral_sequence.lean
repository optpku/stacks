/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
public import stacks_project.Chap92.Lemma_92_12_1
public import stacks_project.Chap92.Lemma_92_7_1_Omega
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quillen spectral sequence

For a surjective ring map `A → B`, the sheaf `omegaSheaf A B` of `underline{B}`-modules
on `PolynomialSite A B` yields a cohomological spectral sequence with
`E₁^{p, q} = H_{-p-q}(PolynomialSite A B, Sym^p (omegaSheaf A B))` abutting to
`Tor^A_{-p-q}(B, B)`, together with vanishing of `H_i` of `Sym^k` for `i < k`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Algebra
open CommAlgCat.Over.Polynomial.Site
open CategoryTheory.CategoryHomology
open FilteredComplex.Cohomology.Convergence
open scoped DerivedTensorChangeOfRings DerivedTensorWithAlgebra

noncomputable section

universe u

namespace Algebra.CotangentComplex.QuillenSpectralSequence

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasProjectiveResolutions ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]

/-- The displayed `E₁^{p, q}`-term `H_{-p-q}(PolynomialSite A B, Sym^p (omegaSheaf A B))`,
as an object of `ModuleCat B`. Homology in negative degree is the zero object. -/
abbrev pageOne (p : ℕ) (q : ℤ) : ModuleCat.{u} B :=
  if 0 ≤ -(p : ℤ) - q then
    moduleHomology (omegaSheaf A B ⋙ ModuleCat.symmetricPower.functor B p)
      (-(p : ℤ) - q).toNat
  else
    ModuleCat.of B PUnit

/-- Unfolding `pageOne` recovers the nonnegative-degree site-homology formula. -/
theorem pageOne_eq (p : ℕ) (q : ℤ) :
    pageOne A B p q =
      if 0 ≤ -(p : ℤ) - q then
        moduleHomology (omegaSheaf A B ⋙ ModuleCat.symmetricPower.functor B p)
          (-(p : ℤ) - q).toNat
      else
        ModuleCat.of B PUnit :=
  sorry

/-- On bidegrees with `-p - q ≥ 0`, the `E₁` term is site homology of the indicated
symmetric power of `omegaSheaf`. -/
theorem pageOne_of_nonneg {p : ℕ} {q : ℤ} (h : 0 ≤ -(p : ℤ) - q) :
    pageOne A B p q =
      moduleHomology (omegaSheaf A B ⋙ ModuleCat.symmetricPower.functor B p)
        (-(p : ℤ) - q).toNat :=
  sorry

/-- On bidegrees with `p + q > 0`, the displayed `E₁` term is the zero object. -/
theorem pageOne_isZero_of_neg {p : ℕ} {q : ℤ} (h : 0 < (p : ℤ) + q) :
    IsZero (pageOne A B p q) :=
  sorry

/-- The abutment `H^n(B ⊗[A]^L[B] B)`, i.e. `Tor^A_{-n}(B, B)` as a `B`-module. -/
abbrev abutment (n : ℤ) : ModuleCat.{u} B :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj (ModuleCat.of A B) ⊗[A]^L[B]
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj (ModuleCat.of B B))

/-- Unfolding `abutment` recovers homology of the change-of-rings derived tensor
`B ⊗[A]^L[B] B`. -/
theorem abutment_eq (n : ℤ) :
    abutment A B n =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj (ModuleCat.of A B) ⊗[A]^L[B]
          (DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj (ModuleCat.of B B)) :=
  sorry

/-- Convergence of a cohomological spectral sequence to Quillen's Tor abutment means
convergence from a filtered complex whose underlying homology identifies with `abutment`. -/
def ConvergesTo (E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0) : Prop :=
  ∃ F : FilteredComplex (ModuleCat.{u} B),
    Converges F E ∧
      ∀ n : ℤ, Nonempty (F.underlying.homology n ≅ abutment A B n)

namespace ConvergesTo

/-- The filtered-complex specification of convergence to the Quillen abutment. -/
theorem spec {E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0} :
    ConvergesTo A B E ↔
      ∃ F : FilteredComplex (ModuleCat.{u} B),
        Converges F E ∧
          ∀ n : ℤ, Nonempty (F.underlying.homology n ≅ abutment A B n) :=
  sorry

end ConvergesTo

/-- A Quillen spectral sequence has first page `pageOne` and converges to `abutment`. -/
def IsQuillen (E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0) : Prop :=
  (∀ p : ℕ, ∀ q : ℤ, Nonempty ((E.page 1).X (p, q) ≅ pageOne A B p q)) ∧
    ConvergesTo A B E

namespace IsQuillen

/-- The first-page and convergence clauses of a Quillen spectral sequence. -/
theorem spec {E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0} :
    IsQuillen A B E ↔
      (∀ p : ℕ, ∀ q : ℤ, Nonempty ((E.page 1).X (p, q) ≅ pageOne A B p q)) ∧
        ConvergesTo A B E :=
  sorry

/-- The first-page entries have the source-prescribed site-homology identification. -/
theorem pageOneIso {E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0}
    (h : IsQuillen A B E) (p : ℕ) (q : ℤ) :
    Nonempty ((E.page 1).X (p, q) ≅ pageOne A B p q) :=
  sorry

/-- A Quillen spectral sequence converges to the displayed Tor abutment. -/
theorem converges {E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0}
    (h : IsQuillen A B E) : ConvergesTo A B E :=
  sorry

end IsQuillen

/-- Theorem 92.12.4 (Quillen spectral sequence) (1). If `algebraMap A B` is surjective,
there is a cohomological spectral sequence `E` in `ModuleCat B` whose first page
identifies with `pageOne`, i.e. `H_{-p-q}(PolynomialSite A B, Sym^p (omegaSheaf A B))`,
and which converges to `abutment`, i.e. `Tor^A_{-n}(B, B)` as a `B`-module.
The differential `d_r` has bidegree `(r, -r+1)` because `E` is a
`CohomologicalSpectralSequence`. -/
@[stacks 08RF]
theorem exists_spectralSequence (hsurj : Function.Surjective (algebraMap A B)) :
    ∃ E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0, IsQuillen A B E :=
  sorry

/-- Theorem 92.12.4 (Quillen spectral sequence) (2). If `algebraMap A B` is surjective,
then `H_i(PolynomialSite A B, Sym^k (omegaSheaf A B))` vanishes for `i < k`. -/
@[stacks 08RF]
theorem omegaSheaf_symmetricPower_isZero_of_lt
    (hsurj : Function.Surjective (algebraMap A B)) (k : ℕ) {i : ℕ} (h_lt : i < k) :
    IsZero (moduleHomology (omegaSheaf A B ⋙ ModuleCat.symmetricPower.functor B k) i) :=
  sorry

end Algebra.CotangentComplex.QuillenSpectralSequence
