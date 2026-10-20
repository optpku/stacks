module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.FittingIdeal.Operations
public import ReasLib.RingTheory.Flatness.LocallyFree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fitting-ideal criterion for finite locally free modules

@stack 07ZD
-/

@[expose] public section

open scoped FittingIdeal

universe u v

namespace FittingIdeal

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A finite module is finite locally free of rank `r` exactly when its Fitting ideals vanish
below `r` and are the unit ideal from `r` onward. -/
@[stacks 07ZD "finite locally free modules detected by Fitting ideals"]
theorem finiteLocallyFreeOfRank_tfae (r : ℕ) :
    List.TFAE
      [ Module.FiniteLocallyFreeOfRank R M r
      , precedingFittingIdeal R M r = ⊥ ∧ Fit[R]_(r)(M) = ⊤
      , (∀ k, k < r → Fit[R]_(k)(M) = ⊥) ∧ ∀ k, r ≤ k → Fit[R]_(k)(M) = ⊤
      ] := sorry

end FittingIdeal
