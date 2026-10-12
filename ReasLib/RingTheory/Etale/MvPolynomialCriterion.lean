/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.Etale
public import ReasLib.RingTheory.KrullDimension.Polynomial
public import ReasLib.RingTheory.Unramified.Kaehler
public import Mathlib.Tactic.CrossRefAttribute

/-!
# An etale criterion over a polynomial algebra

This leaf packages the local-dimension and coordinate-differential criterion
for a finite-type algebra over a polynomial ring.  The criterion is kept next
to the canonical `Algebra.Etale` API rather than in its source chapter.

@stack 0G1C
-/

@[expose] public section

universe u v

namespace Algebra.Etale

/-- Lemma 10.151.9: a finite-type algebra over `k[x_1, ..., x_n]` is etale
exactly when every maximal localization has dimension `n` and the coordinate
differentials generate `Omega[A/k]`. -/
@[stacks 0G1C "polynomial etale criterion"]
theorem mvPolynomial_iff_localDimension_and_differentials
    {k : Type u} [Field k]
    {A : Type v} [CommRing A] [Algebra k A]
    {n : ℕ} [Algebra (MvPolynomial (Fin n) k) A]
    [IsScalarTower k (MvPolynomial (Fin n) k) A]
    [Algebra.FiniteType (MvPolynomial (Fin n) k) A] :
    Algebra.Etale (MvPolynomial (Fin n) k) A ↔
      ((∀ m : MaximalSpectrum A,
          ringKrullDim (Localization.AtPrime m.asIdeal) = n) ∧
        Submodule.span A
          (Set.range fun i : Fin n ↦
            KaehlerDifferential.D k A
              (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i))) = ⊤) := sorry

end Algebra.Etale
