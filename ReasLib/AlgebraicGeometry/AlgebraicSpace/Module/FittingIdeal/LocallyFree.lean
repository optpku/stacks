module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal

/-!
# Finite local freeness detected by Fitting ideal sheaves on algebraic spaces

The Fitting ideal sheaves of a finite-type quasi-coherent module detect whether it is finite
locally free of a specified rank, with the Fitting ideal of index `-1` defined to be zero.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The Fitting ideal sheaf one step below the indicated rank, with the predecessor of the
zeroth Fitting ideal sheaf defined to be the zero ideal sheaf. -/
abbrev precedingFittingIdealSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (r : ℕ) : IdealSubobject X :=
  match r with
  | 0 => ⊥
  | r + 1 => fittingIdealSheaf F r

/-- The predecessor of the zeroth Fitting ideal sheaf is the zero ideal sheaf. -/
@[simp]
theorem precedingFittingIdealSheaf_zero {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) : precedingFittingIdealSheaf F 0 = ⊥ :=
  rfl

/-- The predecessor of the `(r + 1)`st Fitting ideal sheaf is the `r`th Fitting ideal sheaf. -/
@[simp]
theorem precedingFittingIdealSheaf_succ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (r : ℕ) :
    precedingFittingIdealSheaf F (r + 1) = fittingIdealSheaf F r :=
  rfl

/-- A finite-type quasi-coherent module on an algebraic space is finite locally free of
rank `r` if and only if its predecessor and `r`th Fitting ideal sheaves are respectively
zero and unit, equivalently if all its Fitting ideal sheaves are zero below `r` and unit
from `r` onward. -/
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
