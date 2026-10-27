/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.SectionDivisor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.SectionDivisor

/-!
# Divisor and first Chern class of a nonzero section

Both comparisons retain the scheme-theoretic multiplicities of the zero
subspace and the grading by the given dimension function.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 82.17.2: For a good integral algebraic space and a nonzero global
section of an invertible module, the divisor cycle equals the associated
cycle of the zero subspace in degree `dim_δ(X) - 1`. -/
@[stacks 0EQF] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.meromorphicSectionDivisorCycle_eq_zeroSchemeCycle :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ] [IsIntegral X]
      {L : X.Modules} [isInvertibleObject L] (s : L.sections) (hs : s ≠ 0),
      Hom.meromorphicSectionDivisorCycle f δ (toMeromorphicSection s)
          (@toMeromorphicSection_isRegular S X
            (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance L inferInstance s hs) =
        @ClosedSubspace.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f)
          (zeroScheme L s) (Hom.relativeDimensionFunction f δ)
          (Hom.deltaDimension f δ (univIrreducibleClosed X) - 1))

/- The first Chern class capped with the fundamental cycle is the same
zero-subspace cycle's class in the Chow group. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.firstChernCapFundamental_eq_zeroSchemeCycle :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ] [IsIntegral X]
      {L : X.Modules} [isInvertibleObject L] (s : L.sections) (hs : s ≠ 0),
      Hom.firstChernCapFundamental f δ L =
        Hom.chowClass f δ
          (@ClosedSubspace.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f)
            (zeroScheme L s) (Hom.relativeDimensionFunction f δ)
            (Hom.deltaDimension f δ (univIrreducibleClosed X) - 1)))
