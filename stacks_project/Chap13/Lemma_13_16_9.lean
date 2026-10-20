/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Functor.Derived.Exact
import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
import StacksCheckRecall.CommandCrossRef

@[expose] public section

open CategoryTheory

/- Lemma 13.16.9 (Stacks 015F): the functor on derived categories induced by an
exact functor is its right-derived functor. Every object and complex computes it,
and its positive derived degrees vanish. -/

@[stacks 015F]
#check @CategoryTheory.Functor.mapDerivedCategoryFactors

/- Companion checks: exact functors can be bundled once, after which the
induced derived functor, homology comparison, and composition comparison no
longer require repeated exactness or additivity arguments. -/
@[stacks 015F]
#check @CategoryTheory.ExactFunctor.mapDerivedCategory

@[stacks 015F]
#check @CategoryTheory.ExactFunctor.MapDerivedCategory.map

@[stacks 015F]
#check @CategoryTheory.ExactFunctor.MapDerivedCategory.map_app_Q

@[stacks 015F]
#check @CategoryTheory.ExactFunctor.MapDerivedCategory.functor

@[stacks 015F]
#check @CategoryTheory.ExactFunctor.homologyFunctorIso

@[stacks 015F]
#check @CategoryTheory.ExactFunctor.homologyIso_hom_naturality

@[stacks 015F]
#check @CategoryTheory.ExactFunctor.homologyIso_inv_naturality

@[stacks 015F]
#check @CategoryTheory.Functor.MapDerivedCategory.functorIso

@[stacks 015F]
#check @CategoryTheory.ExactFunctor.MapDerivedCategory.compFunctorIso

@[stacks 015F]
#check @CategoryTheory.ExactFunctor.MapDerivedCategory.compFunctorIso_hom_app_Q

@[stacks 015F]
#check @CategoryTheory.Functor.RightDerived.Exact.isRightDerived

@[stacks 015F]
#check @CategoryTheory.Functor.RightDerived.Exact.isAcyclic

@[stacks 015F]
#check @CategoryTheory.Functor.RightDerived.Exact.Bounded.everywhereDefined

@[stacks 015F]
#check @CategoryTheory.Functor.RightDerived.Exact.everywhereDefined

@[stacks 015F]
#check @CategoryTheory.Functor.RightDerived.Exact.Bounded.computesAt

@[stacks 015F]
#check @CategoryTheory.Functor.RightDerived.Exact.computesAt

@[stacks 015F]
#check @CategoryTheory.Functor.RightDerived.Exact.Bounded.vanishesAboveZero

@[stacks 015F]
#check @CategoryTheory.Functor.RightDerived.Exact.vanishesAboveZero
