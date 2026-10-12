/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Minus.Localization
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive Localizers for Bounded-Above Termwise Complexes

This file records the additive structure carried by the canonical inclusions used to localize
bounded-above termwise complexes. Named instances keep downstream resolution constructions from
depending on unfolding the localizer-morphism constructors.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.Minus

variable (A : Type u) [Category.{v} A] [Preadditive A] [CategoryWithHomology A]

/-- The localizer from bounded-above complexes to all complexes has an additive underlying
functor. -/
@[stacks 0643 "additivity of the bounded-above localizer"]
instance localizerFunctorAdditive : (localizer A).functor.Additive := sorry

namespace TermsIn

/-- The localizer from termwise-`P` bounded-above complexes to bounded-above complexes has an
additive underlying functor. -/
@[stacks 0643 "additivity of the termwise bounded-above localizer"]
instance localizerOnMinusFunctorAdditive (P : ObjectProperty A) :
    (localizerOnMinus A P).functor.Additive := sorry

end TermsIn

variable (P : ObjectProperty A)

end CochainComplex.Minus
