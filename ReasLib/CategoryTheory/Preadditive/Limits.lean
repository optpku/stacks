/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additivity of Limit Functors

This leaf records the canonical additivity of the limit functor on diagram categories in a
preadditive target. It is independent of a particular indexing category, derived category, or
geometric application.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe vJ uJ vA uA

namespace CategoryTheory.Limits

variable {J : Type uJ} [Category.{vJ} J]
  {A : Type uA} [Category.{vA} A] [Preadditive A]

/-- The limit functor on `A`-valued `J`-diagrams is additive whenever the required limits exist. -/
instance limitFunctor_additive [HasLimitsOfShape J A] :
    (lim : (J ⥤ A) ⥤ A).Additive := sorry

end CategoryTheory.Limits
