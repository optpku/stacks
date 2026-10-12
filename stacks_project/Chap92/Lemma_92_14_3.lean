/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RingTheory.Extension.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.RingTheory.Ideal.KoszulRegular
public import stacks_project.Chap110.Lemma_110_43_1_Cotangent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent complex of a Koszul-regular quotient

Lemma 92.14.3 identifies `L_{B/A}` in `D(B)` with the conormal module `I/I²`
placed in cohomological degree `-1`, whenever `A → B` is surjective with
Koszul-regular kernel.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra

universe u

noncomputable section

namespace Algebra.CotangentComplex

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Lemma 92.14.3. Let `A → B` be a surjective ring map whose kernel `I` is Koszul.
Then `L_{B/A}` is quasi-isomorphic to `I/I²[1]`. Recorded here as an isomorphism in
`D(B)` between `DerivedCategory.Q.obj (Algebra.cotangentComplex A B)` and the image of
`ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent` under
`DerivedCategory.singleFunctor` in cohomological degree `-1`. -/
@[stacks 08SK]
theorem isIsomorphic_single_conormal
    (h : Function.Surjective (algebraMap A B))
    (hI : (RingHom.ker (algebraMap A B)).IsKoszulRegularIdeal) :
    IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) (-1 : ℤ)).obj
        (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent)) :=
  sorry

/-- If `A → B` is surjective with Koszul-regular kernel, then the André-Quillen homology of
`L_{B/A}` vanishes in every cohomological degree other than `-1`. -/
theorem homology_isZero_of_ne_negOne
    (h : Function.Surjective (algebraMap A B))
    (hI : (RingHom.ker (algebraMap A B)).IsKoszulRegularIdeal)
    {n : ℤ} (hn : n ≠ -1) :
    IsZero ((Algebra.cotangentComplex A B).homology n) :=
  sorry

/-- If `A → B` is surjective with Koszul-regular kernel, then `H^{-1}(L_{B/A})` is isomorphic
to the conormal module `I/I²` as an object of `ModuleCat B`. -/
theorem homology_negOne_isIsomorphic
    (h : Function.Surjective (algebraMap A B))
    (hI : (RingHom.ker (algebraMap A B)).IsKoszulRegularIdeal) :
    IsIsomorphic
      ((Algebra.cotangentComplex A B).homology (-1))
      (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent) :=
  sorry

end

/-- Specialization of the Koszul-regular concentration isomorphism to the quotient algebra
`A ⧸ I`, with conormal module `I.Cotangent`. -/
theorem quotient_isIsomorphic_single_conormal {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.IsKoszulRegularIdeal) :
    IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A (A ⧸ I)))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I)) (-1 : ℤ)).obj
        (ModuleCat.of (A ⧸ I) I.Cotangent)) :=
  sorry

end Algebra.CotangentComplex

end
