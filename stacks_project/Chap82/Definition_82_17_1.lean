/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.WeilDivisor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FirstChernFundamental
import StacksCheckRecall

/-!
# Definition 82.17.1

The `(n-1)`-cycle of a nonzero meromorphic section of an invertible module on
a good integral algebraic space, and the class `c1(L) ∩ [X]` in `CH_{n-1}(X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

/- Definition 82.17.1 (1): In Situation 82.2.1, for good integral `X / B` with
`n = dim_δ(X)` and an invertible `𝒪_X`-module `L`, any nonzero meromorphic
section `s` of `L` determines the `(n-1)`-cycle
`div_L(s) = Hom.meromorphicSectionDivisorCycle f δ s hs`, equal to the Weil
divisor of Spaces over Fields, Definition 72.7.4, viewed as an `(n-1)`-cycle by
Lemma 82.12.1. -/
@[stacks 0EQE]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.meromorphicSectionDivisorCycle :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] {L : X.Modules}
    [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s),
    Function.locallyFinsupp (Points X) ℤ)

/- Definition 82.17.1 (2): In Situation 82.2.1, for good integral `X / B` with
`n = dim_δ(X)` and an invertible `𝒪_X`-module `L`, the Weil divisor associated
to `L` is `c1(L) ∩ [X] = Hom.firstChernCapFundamental f δ L`, the class of
`div_L(s)` in `CH_{n-1}(X)` for any nonzero meromorphic section `s` of `L`,
well-defined by Spaces over Fields, Lemma 72.7.3. -/
@[stacks 0EQE]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.firstChernCapFundamental :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (L : X.Modules) [isInvertibleObject L],
    Hom.codimOneChowGroup f δ)

#check (AlgebraicGeometry.AlgebraicSpace.isRegularMeromorphicSection_iff_ne_zero :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules) [isInvertibleObject L] (s : meromorphicSections X L),
    IsRegularMeromorphicSection X L s ↔ s ≠ 0)
