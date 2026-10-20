/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.HahnSeries.RationalExponentPolynomial
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AffineCompletion
import StacksCheckRecall

/-!
# Completing along V(I) versus V(√I)

If `X = Spec(A)` and `T = V(I)` for finitely generated `I`, then `X_/T` is
`Spf` of the `I`-adic completion. Replacing `I` by `√I` need not yield an
isomorphic completed ring, as shown by `RationalExponentPolynomial`.

Local authorized erratum to the displayed source example: the finite polynomial
union is not local or a valuation ring. Its radical ideal is the augmentation
ideal, which is maximal but not unique. The valuation-ring claim belongs to
the completed series ring. Original uploaded source is retained unchanged.
-/

@[expose] public section

universe u

open CategoryTheory

/- Remark 87.20.9 (Warning) (1): completion of Spec(A) along V(I), for a finitely
generated ideal I, is canonically the formal spectrum of the I-adic completion. -/
@[stacks 0CKX] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.isIso_completionSpfToCompletionAlong_of_fg :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : Type u} [CommRing A]
      (structureHom : AlgebraicGeometry.Spec (.of A) ⟶ S)
      (I : Ideal A), I.FG →
      [CategoryTheory.HasWeakSheafify (AlgebraicGeometry.Scheme.fppfTopology.over S) (Type u)] →
      CategoryTheory.IsIso
        (AlgebraicGeometry.AffineFormalAlgebraicSpace.completionSpfToCompletionAlong
          structureHom I))

/- Remark 87.20.9 (Warning) (2): the canonical radical-completion comparison
need not be bijective. -/
@[stacks 0CKX] #check (RationalExponentPolynomial.not_bijective_mapOfRadical :
  ∀ (κ : Type u) [Field κ], ¬ Function.Bijective
    (AdicCompletion.comparisonRingHomOfPowLe
      (Ideal.span {RationalExponentPolynomial.t κ})
      (Ideal.span {RationalExponentPolynomial.t κ}).radical 1
      (by simpa only [pow_one] using
        (Ideal.span {RationalExponentPolynomial.t κ}).le_radical)))

/- Remark 87.20.9 (Warning) (3): the radical of (t) is the maximal
augmentation ideal of the finite polynomial union. -/
@[stacks 0CKX] #check (RationalExponentPolynomial.radical_span_t_eq_augmentationIdeal :
  ∀ (κ : Type u) [Field κ],
    (Ideal.span {RationalExponentPolynomial.t κ}).radical =
      RationalExponentPolynomial.augmentationIdeal κ)

/- Remark 87.20.9 (Warning) (4): the augmentation ideal satisfies J² = J. -/
@[stacks 0CKX] #check (RationalExponentPolynomial.augmentationIdeal_sq_eq :
  ∀ (κ : Type u) [Field κ],
    RationalExponentPolynomial.augmentationIdeal κ ^ 2 =
      RationalExponentPolynomial.augmentationIdeal κ)

/- Remark 87.20.9 (Warning) (5): the canonical residue map identifies the
J-adic completion with the coefficient field. -/
@[stacks 0CKX] #check (RationalExponentPolynomial.bijective_constantCoeffResidue :
  ∀ (κ : Type u) [Field κ],
    Function.Bijective (RationalExponentPolynomial.constantCoeffResidue κ))

/- Remark 87.20.9 (Warning) (6): the t-adic completion is the rational-exponent
series valuation ring of Example 87.13.2. -/
@[stacks 0CKX] #check (RationalExponentPolynomial.toAdicSeries_bijective :
  ∀ (κ : Type u) [Field κ],
    Function.Bijective (RationalExponentPolynomial.toAdicSeries κ))

/- Remark 87.20.9 (Warning) (7): the finite polynomial union injects into its
t-adic completion. -/
@[stacks 0CKX] #check (RationalExponentPolynomial.of_span_t_injective :
  ∀ (κ : Type u) [Field κ], Function.Injective
    (AdicCompletion.of (Ideal.span {RationalExponentPolynomial.t κ})
      (RationalExponentPolynomial κ)))
