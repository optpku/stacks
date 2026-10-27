/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.MeromorphicSection.Tensor
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 72.7.5. Tensor products of nonzero meromorphic sections have additive
Weil divisors and additive Weil divisor classes. -/
@[stacks 0EPV] #check (AlgebraicGeometry.AlgebraicSpace.nonzeroMeromorphicSectionWeilDivisor_tensor :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsLocallyNoetherian X] [IsIntegral X]
    {L N : X.Modules} [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (t : meromorphicSections X N)
    (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X N t),
    nonzeroMeromorphicSectionWeilDivisor (meromorphicSectionTensor s t)
      (isRegularMeromorphicSection_tensor s t hs ht) =
      nonzeroMeromorphicSectionWeilDivisor s hs +
        nonzeroMeromorphicSectionWeilDivisor t ht)

#check (AlgebraicGeometry.AlgebraicSpace.nonzeroMeromorphicSectionWeilDivisor_tensor_coeff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsLocallyNoetherian X] [IsIntegral X]
    {L N : X.Modules} [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (t : meromorphicSections X N)
    (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X N t)
    (Z : PrimeDivisor X),
    (nonzeroMeromorphicSectionWeilDivisor (meromorphicSectionTensor s t)
        (isRegularMeromorphicSection_tensor s t hs ht)).coeff Z =
      (nonzeroMeromorphicSectionWeilDivisor s hs).coeff Z +
        (nonzeroMeromorphicSectionWeilDivisor t ht).coeff Z)

#check (AlgebraicGeometry.AlgebraicSpace.invertibleModuleWeilDivisorClass_tensor :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsLocallyNoetherian X] [IsIntegral X]
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N],
    invertibleModuleWeilDivisorClass (L ⊗ N) =
      invertibleModuleWeilDivisorClass L + invertibleModuleWeilDivisorClass N)

#check (AlgebraicGeometry.AlgebraicSpace.meromorphicSectionTensor_ne_zero :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsLocallyNoetherian X] [IsIntegral X]
      {L N : X.Modules} [isInvertibleObject L] [isInvertibleObject N]
      (s : meromorphicSections X L) (t : meromorphicSections X N)
      (hs : s ≠ 0) (ht : t ≠ 0), meromorphicSectionTensor s t ≠ 0)

#check (AlgebraicGeometry.AlgebraicSpace.isRegularMeromorphicSection_iff_ne_zero :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsLocallyNoetherian X] [IsIntegral X]
      (L : X.Modules) [isInvertibleObject L] (s : meromorphicSections X L),
      IsRegularMeromorphicSection X L s ↔ s ≠ 0)
