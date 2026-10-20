/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Plus.Localization
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive Localizers for Bounded-Below Termwise Complexes

This file records the additive structure carried by the canonical inclusions used to localize
bounded-below termwise complexes. Named instances keep downstream resolution constructions from
depending on unfolding the localizer-morphism constructors.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.Plus

variable (A : Type u) [Category.{v} A] [Preadditive A] [CategoryWithHomology A]

/-- The localizer from bounded-below complexes to all complexes has an additive underlying
functor. -/
@[stacks 05T6 "additivity of the bounded-below localizer"]
instance localizerFunctorAdditive : (localizer A).functor.Additive := sorry

namespace TermsIn

/-- The localizer from termwise-`P` bounded-below complexes to bounded-below complexes has an
additive underlying functor. -/
@[stacks 05T6 "additivity of the termwise bounded-below localizer"]
instance localizerOnPlusFunctorAdditive (P : ObjectProperty A) :
    (localizerOnPlus A P).functor.Additive := sorry

end TermsIn

variable (P : ObjectProperty A)

end CochainComplex.Plus
