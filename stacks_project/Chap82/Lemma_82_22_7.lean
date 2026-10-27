/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin.ClosedSubspace
import StacksCheckRecall

/-!
# Gysin pullback of closed-subspace cycles

On a good algebraic space, the refined Gysin map of a section of an invertible
module sends the cycle of a closed subspace to the cycle of its scheme-theoretic
intersection with the zero scheme, when that intersection is an effective
Cartier divisor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function

noncomputable section

universe u

/- Lemma 82.22.7: In Situation 82.2.1 let `X / B` be good. Let
`(L, s, i : D ⟶ X)` be as in Definition 82.22.1. Let `Z ⊂ X` be a closed
subspace such that `dim_δ(Z) ≤ k + 1` and such that `D ∩ Z` is an effective
Cartier divisor on `Z`. Then `i*([Z]_{k+1}) = [D ∩ Z]_k` in `CH_k(D)`. -/
@[stacks 0ER7] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.gysin_closedSubspaceCycle :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (L : X.Modules) [isInvertibleObject L]
      (s : L.sections) (Z : ClosedSubspace X) (k : ℤ)
      (hZ : Hom.closedSubspaceDeltaDimension f δ Z ≤ ((k + 1 : ℤ) : EInt))
      [IsEffectiveCartierDivisor ((zeroScheme L s).inverseImageSubspace Z.ι).ι],
    Hom.gysin f δ k L s
        ⟨Hom.closedSubspaceCycle f δ Z (k + 1) hZ,
          Hom.closedSubspaceCycle_mem_cycleGroup f δ Z (k + 1) hZ⟩ =
      Hom.chowMk (zeroSchemeι L s ≫ f) δ k
        ⟨@ClosedSubspace.associatedCycle S (zeroScheme L s).X
            (LocallyOfFiniteType.isLocallyNoetherian (zeroSchemeι L s ≫ f))
            (Z.inverseImageSubspace (zeroSchemeι L s))
            (Hom.relativeDimensionFunction (zeroSchemeι L s ≫ f) δ) k,
          Hom.associatedCycle_inverseImage_mem f δ L s Z k hZ⟩)
