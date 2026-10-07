module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_14_6
public import stacks_project.Chap87.Remark_87_20_9_Warning_Comparison
public import stacks_project.Chap87.Remark_87_20_9_Warning_Polynomial
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

noncomputable section

universe u

open AdicCompletion RationalExponentPolynomial

/- Remark 87.20.9 (Warning) (1): if `X = Spec(A)` and `T = V(I)` for a finitely
generated ideal `I ⊆ A`, then `X_/T = Spf` of the `I`-adic completion, as the
identification that `toCompletionAlong` is bijective on quasi-compact schemes
over `S`. -/
@[stacks 0CKX] #check
  AlgebraicGeometry.AffineFormalAlgebraicSpace.bijective_toCompletionAlong_app

/-- Remark 87.20.9 (Warning) (2): the canonical map from the `I`-adic completion
to the radical-adic completion need not be bijective. -/
@[stacks 0CKX]
theorem not_bijective_mapOfRadical (κ : Type u) [Field κ] :
    ¬ Function.Bijective (mapOfRadical (Ideal.span {t κ})) :=
  sorry

/-- Remark 87.20.9 (Warning) (3): for `A = ⋃ n, κ[t^{1/n}]`, the radical of
`(t)` is the augmentation ideal. -/
@[stacks 0CKX]
theorem radical_span_t_eq_augmentationIdeal (κ : Type u) [Field κ] :
    (Ideal.span {t κ}).radical = augmentationIdeal κ :=
  sorry

/-- Remark 87.20.9 (Warning) (4): the augmentation ideal of `A` satisfies `J ^ 2 = J`. -/
@[stacks 0CKX]
theorem augmentationIdeal_sq_eq (κ : Type u) [Field κ] :
    augmentationIdeal κ ^ 2 =
      augmentationIdeal κ :=
  sorry

/-- Remark 87.20.9 (Warning) (5): the `J`-adic completion of `A` is `κ`. -/
@[stacks 0CKX]
theorem bijective_constantCoeffResidue (κ : Type u) [Field κ] :
    Function.Bijective (constantCoeffResidue κ) :=
  sorry

/-- Remark 87.20.9 (Warning) (6): the `I`-adic completion of `A` is the
valuation ring of Example 87.13.2. -/
@[stacks 0CKX]
theorem toAdicSeries_bijective (κ : Type u) [Field κ] :
    Function.Bijective (toAdicSeries κ) :=
  sorry

/-- Remark 87.20.9 (Warning) (7): `A` injects into its `I`-adic completion. -/
@[stacks 0CKX]
theorem of_span_t_injective (κ : Type u) [Field κ] :
    Function.Injective
      (AdicCompletion.of (Ideal.span {t κ}) (RationalExponentPolynomial κ)) :=
  sorry
