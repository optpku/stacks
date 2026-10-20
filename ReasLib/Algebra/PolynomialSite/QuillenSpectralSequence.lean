module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
public import ReasLib.Algebra.PolynomialSite.Differentials
public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower
public import ReasLib.CategoryTheory.Sites.CategoryHomology.Module
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

/-- The first-page term in bidegree `(p, q)` is the homology of the `p`th symmetric
power of the differential sheaf in degree `-p-q`, extended by zero in negative degree. -/
abbrev pageOne (p : ℕ) (q : ℤ) : ModuleCat.{u} B :=
  if 0 ≤ -(p : ℤ) - q then
    moduleHomology (omegaSheaf A B ⋙ ModuleCat.symmetricPower.functor B p)
      (-(p : ℤ) - q).toNat
  else
    ModuleCat.of B PUnit

/-- First-page terms are symmetric-power site homology in nonnegative degree and
the zero module in negative degree. -/
theorem pageOne_eq (p : ℕ) (q : ℤ) :
    pageOne A B p q =
      if 0 ≤ -(p : ℤ) - q then
        moduleHomology (omegaSheaf A B ⋙ ModuleCat.symmetricPower.functor B p)
          (-(p : ℤ) - q).toNat
      else
        ModuleCat.of B PUnit :=
  sorry

/-- In nonnegative homological degree, a first-page term is the site homology
of the corresponding symmetric power of the differential sheaf. -/
theorem pageOne_of_nonneg {p : ℕ} {q : ℤ} (h : 0 ≤ -(p : ℤ) - q) :
    pageOne A B p q =
      moduleHomology (omegaSheaf A B ⋙ ModuleCat.symmetricPower.functor B p)
        (-(p : ℤ) - q).toNat :=
  sorry

/-- First-page terms vanish when the sum of their bidegrees is positive. -/
theorem pageOne_isZero_of_neg {p : ℕ} {q : ℤ} (h : 0 < (p : ℤ) + q) :
    IsZero (pageOne A B p q) :=
  sorry

/-- The degree-`n` cohomology of the derived self-tensor product of `B` over `A`,
regarded as a `B`-module, is the Tor abutment in degree `-n`. -/
abbrev abutment (n : ℤ) : ModuleCat.{u} B :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj (ModuleCat.of A B) ⊗[A]^L[B]
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj (ModuleCat.of B B))

/-- The Tor abutment is computed by cohomology of the change-of-rings derived
tensor product of the complexes concentrated in degree zero at `B`. -/
theorem abutment_eq (n : ℤ) :
    abutment A B n =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj (ModuleCat.of A B) ⊗[A]^L[B]
          (DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj (ModuleCat.of B B)) :=
  sorry

/-- A spectral sequence converges to the Tor abutment if it converges from a
filtered complex whose underlying cohomology is isomorphic to the derived self-tensor
cohomology of `B` over `A`. -/
def ConvergesTo (E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0) : Prop :=
  ∃ F : FilteredComplex (ModuleCat.{u} B),
    Converges F E ∧
      ∀ n : ℤ, Nonempty (F.underlying.homology n ≅ abutment A B n)

namespace ConvergesTo

/-- Convergence to the Tor abutment is equivalent to the existence of a convergent
filtered complex with the prescribed underlying cohomology. -/
theorem spec {E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0} :
    ConvergesTo A B E ↔
      ∃ F : FilteredComplex (ModuleCat.{u} B),
        Converges F E ∧
          ∀ n : ℤ, Nonempty (F.underlying.homology n ≅ abutment A B n) :=
  sorry

end ConvergesTo

/-- A Quillen spectral sequence has symmetric-power site homology in its nonnegative
first-page columns, zero negative columns, and convergence to the Tor abutment. -/
def IsQuillen (E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0) : Prop :=
  (∀ p : ℕ, ∀ q : ℤ, Nonempty ((E.page 1).X (p, q) ≅ pageOne A B p q)) ∧
    ((∀ p q : ℤ, p < 0 → IsZero ((E.page 1).X (p, q))) ∧ ConvergesTo A B E)

namespace IsQuillen

/-- The Quillen condition is equivalent to its nonnegative-column identifications,
negative-column vanishing, and convergence to the Tor abutment. -/
theorem spec {E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0} :
    IsQuillen A B E ↔
      (∀ p : ℕ, ∀ q : ℤ, Nonempty ((E.page 1).X (p, q) ≅ pageOne A B p q)) ∧
        ((∀ p q : ℤ, p < 0 → IsZero ((E.page 1).X (p, q))) ∧ ConvergesTo A B E) :=
  sorry

/-- The nonnegative first-page columns of a Quillen spectral sequence are
isomorphic to the corresponding symmetric-power site homology objects. -/
theorem pageOneIso {E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0}
    (h : IsQuillen A B E) (p : ℕ) (q : ℤ) :
    Nonempty ((E.page 1).X (p, q) ≅ pageOne A B p q) :=
  sorry

/-- A Quillen spectral sequence converges to the derived self-tensor Tor abutment. -/
theorem converges {E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0}
    (h : IsQuillen A B E) : ConvergesTo A B E :=
  sorry

end IsQuillen

/-- If `algebraMap A B` is surjective,
there is a cohomological spectral sequence `E` in `ModuleCat B` whose first page
identifies with `pageOne`, i.e. `H_{-p-q}(PolynomialSite A B, Sym^p (omegaSheaf A B))`,
and which converges to `abutment`, i.e. `Tor^A_{-n}(B, B)` as a `B`-module.
The differential `d_r` has bidegree `(r, -r+1)` because `E` is a
`CohomologicalSpectralSequence`. -/
@[stacks 08RF]
theorem exists_spectralSequence (hsurj : Function.Surjective (algebraMap A B)) :
    ∃ E : CohomologicalSpectralSequence (ModuleCat.{u} B) 0, IsQuillen A B E :=
  sorry

/-- If `algebraMap A B` is surjective,
then `H_i(PolynomialSite A B, Sym^k (omegaSheaf A B))` vanishes for `i < k`. -/
@[stacks 08RF]
theorem omegaSheaf_symmetricPower_isZero_of_lt
    (hsurj : Function.Surjective (algebraMap A B)) (k : ℕ) {i : ℕ} (h_lt : i < k) :
    IsZero (moduleHomology (omegaSheaf A B ⋙ ModuleCat.symmetricPower.functor B k) i) :=
  sorry

end Algebra.CotangentComplex.QuillenSpectralSequence
