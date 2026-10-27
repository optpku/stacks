/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.MeromorphicSection.ClassGroup
import StacksCheckRecall

/-!
# Definition 72.7.4

The Weil divisor of a nonzero meromorphic section of an invertible module,
and the Weil divisor class of the module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace CategoryTheory.MonoidalCategory

universe u

/- Definition 72.7.4 (1): Let `S` be a scheme. Let `X` be a locally Noetherian
integral algebraic space over `S`. Let `L` be an invertible `𝒪_X`-module.
For any nonzero meromorphic section `s` of `L` the Weil divisor associated to
`s` is `nonzeroMeromorphicSectionWeilDivisor s hs`, the locally finite sum
`∑ ord_{Z, L}(s) [Z]` in `Div(X)`, well-defined by Lemma 72.7.2. -/
@[stacks 0EPU] #check (AlgebraicGeometry.AlgebraicSpace.nonzeroMeromorphicSectionWeilDivisor :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X] {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s),
    WeilDivisor X)

#check (AlgebraicGeometry.AlgebraicSpace.nonzeroMeromorphicSectionWeilDivisor_coeff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X] {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X),
    (nonzeroMeromorphicSectionWeilDivisor s hs).coeff Z = MeromorphicSection.ord s hs Z)

/- Definition 72.7.4 (2): Let `S` be a scheme. Let `X` be a locally Noetherian
integral algebraic space over `S`. Let `L` be an invertible `𝒪_X`-module.
The Weil divisor class associated to `L` is the image of
`nonzeroMeromorphicSectionWeilDivisor s hs` in `Cl(X)` for any nonzero
meromorphic section `s` of `L`, well-defined by Lemma 72.7.3. -/
@[stacks 0EPU] #check (AlgebraicGeometry.AlgebraicSpace.invertibleModuleWeilDivisorClass_eq :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules) [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s),
    invertibleModuleWeilDivisorClass L =
      nonzeroMeromorphicSectionWeilDivisorClass s hs)

#check (AlgebraicGeometry.AlgebraicSpace.invertibleModuleWeilDivisorClass :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules) [isInvertibleObject L],
    WeilDivisorClassGroup X)
