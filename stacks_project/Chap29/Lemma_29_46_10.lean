/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.PolynomialQuotient

open CategoryTheory

universe u

/- Lemma 29.46.10 (1): if `x ^ 3 = y ^ 2`, then the map
`A → A[t] / (t ^ 2 - x, t ^ 3 - y)` induces isomorphisms on residue fields. -/
@[stacks 0EUI] #check
  (AlgebraicGeometry.CuspQuotient.residueFieldMap_isIso :
    ∀ (A : Type u) [CommRing A] (x y : A) (_ : x ^ 3 = y ^ 2),
      let I : Ideal (Polynomial A) := Ideal.span ({Polynomial.X ^ 2 - Polynomial.C x,
        Polynomial.X ^ 3 - Polynomial.C y} : Set (Polynomial A))
      let B : Type u := Polynomial A ⧸ I
      let φ : A →+* B := (Ideal.Quotient.mk I).comp Polynomial.C
      let f : AlgebraicGeometry.Spec (.of B) ⟶ AlgebraicGeometry.Spec (.of A) :=
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)
      ∀ z : AlgebraicGeometry.Spec (.of B), IsIso (f.residueFieldMap z))

/- Lemma 29.46.10 (2): if `x ^ 3 = y ^ 2`, then the map on spectra induced by
`A → A[t] / (t ^ 2 - x, t ^ 3 - y)` is a universal homeomorphism. -/
@[stacks 0EUI] #check
  (AlgebraicGeometry.CuspQuotient.universalHomeomorphism :
    ∀ (A : Type u) [CommRing A] (x y : A) (_ : x ^ 3 = y ^ 2),
      let I : Ideal (Polynomial A) := Ideal.span ({Polynomial.X ^ 2 - Polynomial.C x,
        Polynomial.X ^ 3 - Polynomial.C y} : Set (Polynomial A))
      let B : Type u := Polynomial A ⧸ I
      let φ : A →+* B := (Ideal.Quotient.mk I).comp Polynomial.C
      AlgebraicGeometry.UniversalHomeomorphism
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)))

/- Lemma 29.46.10 (3): if `p` is prime and `(p : A) ^ p * x = y ^ p`, then the map
on spectra induced by `A → A[t] / (t ^ p - x, p * t - y)` is a universal homeomorphism. -/
@[stacks 0EUI] #check
  (AlgebraicGeometry.PrimePowerQuotient.universalHomeomorphism :
    ∀ (A : Type u) [CommRing A] (x y : A) (p : ℕ) (_ : Nat.Prime p)
      (_ : (p : A) ^ p * x = y ^ p),
      let I : Ideal (Polynomial A) := Ideal.span ({Polynomial.X ^ p - Polynomial.C x,
        Polynomial.C (p : A) * Polynomial.X - Polynomial.C y} : Set (Polynomial A))
      let B : Type u := Polynomial A ⧸ I
      let φ : A →+* B := (Ideal.Quotient.mk I).comp Polynomial.C
      AlgebraicGeometry.UniversalHomeomorphism
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)))
