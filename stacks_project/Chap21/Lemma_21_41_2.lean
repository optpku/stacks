/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.SimplicialLowerShriek
import StacksCheckRecall

/-!
# Lemma 21.41.2

The projection lower-shriek and its change-of-rings comparison are reusable simplicial-site
owners.  This file records the textbook item without rebuilding those constructions in the
chapter namespace.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory SimplicialSite

namespace CategoryTheory.SimplicialSite.Derived

/- Lemma 21.41.2: for `α : A ⟶ B`, if the induced unit comparison
`unitComparison α` is an isomorphism in the target derived category, then for every
`K : DerivedCategory (ModuleCat A)` the projection lower shriek agrees, up to isomorphism, with
the lower shriek after derived extension of scalars along `α`. -/
@[stacks 09D2 "Lemma 21.41.2 lower shriek"]
#check @lowerShriek

@[stacks 09D2 "Lemma 21.41.2 derived change of rings"]
#check @tensor

@[stacks 09D2 "Lemma 21.41.2 unit comparison"]
#check @unitComparison

@[stacks 09D2 "Lemma 21.41.2 unit comparison isomorphism"]
#check @unitComparisonIso

@[stacks 09D2 "Lemma 21.41.2 functor comparison"]
#check @tensor.lowerShriek_isomorphic

@[stacks 09D2 "Lemma 21.41.2 objectwise comparison"]
#check @tensor.lowerShriek_obj_isomorphic

end CategoryTheory.SimplicialSite.Derived
