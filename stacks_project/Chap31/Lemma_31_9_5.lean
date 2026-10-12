/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.LocallyFree

universe u

/- Lemma 31.9.5: a finite-type quasi-coherent module on a scheme is finite locally free of
rank `r` if and only if its predecessor and `r`th Fitting ideal sheaves are respectively zero
and unit, equivalently if all its Fitting ideal sheaves are zero below `r` and unit from `r`
onward. -/
@[stacks 0C3G] #check
  (AlgebraicGeometry.Scheme.fittingIdealSheaf_tfae :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (ℱ : S.Modules)
      [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (r : ℕ),
      List.TFAE
        [ SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ
        , AlgebraicGeometry.Scheme.precedingFittingIdealSheaf ℱ r = ⊥ ∧
            AlgebraicGeometry.Scheme.fittingIdealSheaf ℱ r = ⊤
        , (∀ k < r, AlgebraicGeometry.Scheme.fittingIdealSheaf ℱ k = ⊥) ∧
            ∀ k ≥ r, AlgebraicGeometry.Scheme.fittingIdealSheaf ℱ k = ⊤
        ])
