/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RingTheory.Kaehler.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver
public import stacks_project.Chap110.Lemma_110_43_1_Cotangent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent complex of a polynomial algebra

Lemma 92.4.7 identifies `L_{B/A}` in `D(B)` with the Kähler differentials
`Ω[B⁄A]` placed in degree zero, whenever `B` is a polynomial algebra over `A`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra

universe u

namespace Algebra.CotangentComplex

section

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsPolynomial A B]

/-- Lemma 92.4.7. If `B` is a polynomial algebra over the ring `A`, then `L_{B/A}` is
quasi-isomorphic to `Ω[B⁄A][0]`. Recorded here as an isomorphism in `D(B)` between
`DerivedCategory.Q.obj (Algebra.cotangentComplex A B)` and the image of
`ModuleCat.of B Ω[B⁄A]` under `DerivedCategory.singleFunctor` in degree `0`. -/
@[stacks 08QH]
theorem isIsomorphic_single_kaehler :
    IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj
        (ModuleCat.of B Ω[B⁄A])) :=
  sorry

/-- If `B` is a polynomial `A`-algebra, then the André-Quillen homology of `L_{B/A}`
vanishes in every nonzero cohomological degree. -/
theorem homology_isZero_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
    IsZero ((Algebra.cotangentComplex A B).homology n) :=
  sorry

end

/-- The André-Quillen complex of a multivariate polynomial algebra `MvPolynomial σ A`
over `A` is isomorphic in `D(MvPolynomial σ A)` to `Ω[MvPolynomial σ A⁄A]` placed in
degree zero. -/
theorem mvPolynomial_isIsomorphic_single_kaehler (A : Type u) (σ : Type u) [CommRing A] :
    IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A (MvPolynomial σ A)))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial σ A)) (0 : ℤ)).obj
        (ModuleCat.of (MvPolynomial σ A) Ω[MvPolynomial σ A⁄A])) :=
  sorry

end Algebra.CotangentComplex
