/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap71.Lemma_71_5_5_FittingIdeal

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

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.5.5: a finite-type quasi-coherent module on an algebraic space is finite
locally free of rank `r` if and only if its predecessor and `r`th Fitting ideal sheaves
are respectively zero and unit, equivalently if all its Fitting ideal sheaves are zero
below `r` and unit from `r` onward. -/
@[stacks 0CZ8]
theorem fittingIdealSheaf_tfae
    {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    List.TFAE
      [ SheafOfModules.IsFiniteLocallyFreeOfRank r F
      , precedingFittingIdealSheaf F r = ⊥ ∧ fittingIdealSheaf F r = ⊤
      , (∀ k < r, fittingIdealSheaf F k = ⊥) ∧
          ∀ k ≥ r, fittingIdealSheaf F k = ⊤
      ] :=
  sorry

namespace fittingIdealSheaf

/-- A finite-type quasi-coherent module is finite locally free of rank `r` if and only if its
predecessor Fitting ideal sheaf is zero and its `r`th Fitting ideal sheaf is unit. -/
theorem isFiniteLocallyFreeOfRank_iff_preceding_eq_bot_and_eq_top
    {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank r F ↔
      precedingFittingIdealSheaf F r = ⊥ ∧ fittingIdealSheaf F r = ⊤ :=
  sorry

/-- A finite-type quasi-coherent module is finite locally free of rank `r` if and only if its
Fitting ideal sheaves are zero below `r` and unit from `r` onward. -/
theorem isFiniteLocallyFreeOfRank_iff_eq_bot_below_and_eq_top_from
    {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank r F ↔
      (∀ k < r, fittingIdealSheaf F k = ⊥) ∧
        ∀ k ≥ r, fittingIdealSheaf F k = ⊤ :=
  sorry

end fittingIdealSheaf

end AlgebraicGeometry.AlgebraicSpace
