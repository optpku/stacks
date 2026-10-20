/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap72.Lemma_72_7_3_Quotient

/-!
# Weil divisors of meromorphic sections differ by a principal divisor

On a locally Noetherian integral algebraic space, the Weil divisor of a regular
meromorphic section of an invertible module equals the Weil divisor of another
regular section plus the principal Weil divisor of their rational-function unit quotient.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- Lemma 72.7.3: Let `S` be a scheme. Let `X` be a locally Noetherian integral
algebraic space over `S`. Let `L` be an invertible `𝒪_X`-module. Let `s`, `t`
be nonzero meromorphic sections of `L`. Then
`f = meromorphicSectionQuotient s t hs ht` is the actual unit `s / t ∈ R(X)*`,
of type `(RationalFunction X)ˣ`, and the Weil divisors satisfy
`nonzeroMeromorphicSectionWeilDivisor s hs =
nonzeroMeromorphicSectionWeilDivisor t ht +
WeilDivisor.ofRationalUnit (meromorphicSectionQuotient s t hs ht)`. -/
@[stacks 0EPT]
theorem nonzeroMeromorphicSectionWeilDivisor_eq_add_principal
    {L : X.Modules} [isInvertibleObject L]
    (s t : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X L t) :
    nonzeroMeromorphicSectionWeilDivisor s hs =
      nonzeroMeromorphicSectionWeilDivisor t ht +
        WeilDivisor.ofRationalUnit (meromorphicSectionQuotient s t hs ht) :=
  sorry

/-- The identity of Weil divisors of two regular meromorphic sections of the
same invertible module, as an equality of orders along each prime divisor. -/
theorem nonzeroMeromorphicSectionWeilDivisor_eq_add_principal_coeff
    {L : X.Modules} [isInvertibleObject L]
    (s t : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X L t) (Z : PrimeDivisor X) :
    MeromorphicSection.ord s hs Z =
      MeromorphicSection.ord t ht Z +
        Z.ord (meromorphicSectionQuotient s t hs ht) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
