/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.FinitePresentation
public import ReasLib.RingTheory.AdicCompletion.Exactness.ShortComplex

@[expose] public section

universe u

open CategoryTheory

namespace AdicCompletion.Counterexample

/-- There exists a short exact sequence of modules over a commutative ring whose
objectwise adic completion is not exact. -/
theorem exists_shortExact_map_not_exact :
    ∃ (R : Type u) (_ : CommRing R) (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R)),
      S.ShortExact ∧ ¬ (mapShortComplex I S).Exact := sorry

/-- Adic completion at a finitely generated ideal can fail to preserve exactness
of a right exact sequence of finitely presented modules. -/
theorem exists_fg_finitePresentation_not_rightExact :
    ∃ (R : Type u) (_ : CommRing R) (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R)),
      I.FG ∧ Module.FinitePresentation R S.X₁ ∧ Module.FinitePresentation R S.X₂ ∧
        Module.FinitePresentation R S.X₃ ∧ S.Exact ∧ Epi S.g ∧
        ¬ (mapShortComplex I S).Exact := sorry

end AdicCompletion.Counterexample
