/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import ReasLib.CategoryTheory.Abelian.Injective.Characterizations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Characterizations of injective modules

@stack 0AVD

This leaf translates categorical characterizations of injective objects into the traditional
module-level predicate.
-/

@[expose] public section

open CategoryTheory ModuleCat

universe u v

namespace Module

variable (R : Type u) [Ring R] (J : Type v) [AddCommGroup J] [Module R J]

/-- Definition 15.55.1 (0AVD): an `R`-module is injective exactly when its represented
contravariant Hom functor is exact. -/
@[stacks 0AVD "module injectivity as exactness of represented Hom"]
theorem injective_iff_exact_preadditiveYonedaObj :
    Module.Injective R J ↔
      exactFunctor (ModuleCat R)ᵒᵖ _ (preadditiveYonedaObj (of R J)) := sorry

end Module
