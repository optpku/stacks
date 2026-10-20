module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal.LocallyFree

/-!
# Lemma 71.5.5

A finite-type quasi-coherent module on an algebraic space is finite locally free of
rank `r` if and only if its predecessor and `r`th Fitting ideal sheaves are respectively
zero and unit, equivalently if all its Fitting ideal sheaves are zero below `r` and unit
from `r` onward.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.5.5: a finite-type quasi-coherent module on an algebraic space is finite
locally free of rank `r` if and only if its predecessor and `r`th Fitting ideal sheaves
are respectively zero and unit, equivalently if all its Fitting ideal sheaves are zero
below `r` and unit from `r` onward. -/
@[stacks 0CZ8] #check (AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
      [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ),
    List.TFAE
      [ SheafOfModules.IsFiniteLocallyFreeOfRank r F
      , precedingFittingIdealSheaf F r = ⊥ ∧ fittingIdealSheaf F r = ⊤
      , (∀ k < r, fittingIdealSheaf F k = ⊥) ∧
          ∀ k ≥ r, fittingIdealSheaf F k = ⊤
      ])
