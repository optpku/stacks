/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal
public import ReasLib.RingTheory.FittingIdeal.LocallyFree

/-!
# Finite local freeness detected by Fitting ideal sheaves

The Fitting ideal sheaves of a finite-type quasi-coherent module detect whether it is finite
locally free of a specified rank.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite-type quasi-coherent module is finite locally free of rank `r` exactly when its
predecessor and `r`th Fitting ideal sheaves are respectively zero and unit, equivalently when
its Fitting ideal sheaves are zero below `r` and unit from `r` onward. -/
theorem fittingIdealSheaf_tfae
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (r : ℕ) :
    List.TFAE
      [ SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ
      , precedingFittingIdealSheaf ℱ r = ⊥ ∧ fittingIdealSheaf ℱ r = ⊤
      , (∀ k < r, fittingIdealSheaf ℱ k = ⊥) ∧
          ∀ k ≥ r, fittingIdealSheaf ℱ k = ⊤
      ] := sorry

namespace fittingIdealSheaf

/-- A finite-type quasi-coherent module is finite locally free of rank `r` if and only if its
predecessor Fitting ideal sheaf is zero and its `r`th Fitting ideal sheaf is unit. -/
theorem isFiniteLocallyFreeOfRank_iff_preceding_eq_bot_and_eq_top
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ ↔
      precedingFittingIdealSheaf ℱ r = ⊥ ∧ fittingIdealSheaf ℱ r = ⊤ := sorry

/-- A finite-type quasi-coherent module is finite locally free of rank `r` if and only if its
Fitting ideal sheaves are zero below `r` and unit from `r` onward. -/
theorem isFiniteLocallyFreeOfRank_iff_eq_bot_below_and_eq_top_from
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ ↔
      (∀ k < r, fittingIdealSheaf ℱ k = ⊥) ∧
        ∀ k ≥ r, fittingIdealSheaf ℱ k = ⊤ := sorry

end fittingIdealSheaf

end AlgebraicGeometry.Scheme
