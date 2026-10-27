/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.MeromorphicSection.Quotient
import StacksCheckRecall

/-!
# Weil divisors of meromorphic sections differ by a principal divisor
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

/- Lemma 72.7.3: Let `S` be a scheme. Let `X` be a locally Noetherian integral
algebraic space over `S`. Let `L` be an invertible `𝒪_X`-module. Let `s`, `t`
be nonzero meromorphic sections of `L`. Then the Weil divisor identity holds. -/
@[stacks 0EPT] #check
  (AlgebraicGeometry.AlgebraicSpace.nonzeroMeromorphicSectionWeilDivisor_eq_add_principal :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsLocallyNoetherian X] [IsIntegral X] {L : X.Modules}
      [isInvertibleObject L] (s t : meromorphicSections X L)
      (hs : IsRegularMeromorphicSection X L s)
      (ht : IsRegularMeromorphicSection X L t),
      nonzeroMeromorphicSectionWeilDivisor s hs =
        nonzeroMeromorphicSectionWeilDivisor t ht +
          principalWeilDivisor X (meromorphicSectionQuotient s t hs ht))

#check (AlgebraicGeometry.AlgebraicSpace.nonzeroMeromorphicSectionWeilDivisor_eq_add_principal_coeff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsLocallyNoetherian X] [IsIntegral X] {L : X.Modules}
      [isInvertibleObject L] (s t : meromorphicSections X L)
      (hs : IsRegularMeromorphicSection X L s)
      (ht : IsRegularMeromorphicSection X L t) (Z : PrimeDivisor X),
      MeromorphicSection.ord s hs Z =
        MeromorphicSection.ord t ht Z +
          Z.ord (meromorphicSectionQuotient s t hs ht))

end AlgebraicGeometry.AlgebraicSpace
