module

public import ReasLib.RingTheory.FittingIdeal.Basic
public import ReasLib.RingTheory.Flatness.LocallyFree
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open scoped FittingIdeal

universe u v

namespace FittingIdeal

/-- For a finite locally free algebra whose principal localization is étale,
the extended zeroth Fitting ideal factors through the extended ideal; if the
original ideal is finitely generated, so are the Fitting ideal and the factor ideal. -/
@[stacks 0812]
theorem exists_away_factor
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    (d : ℕ) [Module.FiniteLocallyFreeOfRank A C d] (h : C)
    [Algebra.Etale A (Localization.Away h)] (J : Ideal C) :
    ∃ J' : Ideal (Localization.Away h),
      Ideal.map (algebraMap A (Localization.Away h)) (Fit[A]_(0)(C ⧸ J)) =
          Ideal.map (algebraMap C (Localization.Away h)) J * J' ∧
        (J.FG → (Fit[A]_(0)(C ⧸ J)).FG ∧ J'.FG) := sorry

end FittingIdeal
