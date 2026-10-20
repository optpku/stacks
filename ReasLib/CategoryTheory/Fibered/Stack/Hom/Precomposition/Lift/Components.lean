/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition.Lift.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Components of precomposition lift comparisons

This leaf specializes the component API for generic quasi-inverse lifts to precomposition
between stack and ambient Hom categories.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

namespace StackOver.Hom.PrecompLift.mapFunctor

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X X' : FiberedCategoryOver.{u, v, w, vS} C}
variable {Y Y' : StackOver.{u, v, w, vS} J}
variable {i : X ⟶ Y.toFiberedCategoryOver}
variable (i' : X' ⟶ Y'.toFiberedCategoryOver)

namespace comparisonIso.hom

/-- The forward component of the precomposition lift comparison is the chosen counit at the
postcomposite `F ≫ i'`. -/
@[simp, stacks 04W9 "forward component of fixed-universe precomposition comparison"]
theorem app (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    (F : X ⟶ X') :
    (comparisonIso i' q).hom.app F = q.counitIso.hom.app (F ≫ i') := sorry

end comparisonIso.hom

namespace comparisonIso.inv

/-- The inverse component of the precomposition lift comparison is the inverse chosen counit at
the postcomposite `F ≫ i'`. -/
@[simp, stacks 04W9 "inverse component of fixed-universe precomposition comparison"]
theorem app (q : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    (F : X ⟶ X') :
    (comparisonIso i' q).inv.app F = q.counitIso.inv.app (F ≫ i') := sorry

end comparisonIso.inv

namespace choiceIso.hom

/-- The forward component comparing two precomposition lifts is the canonical comparison of the
chosen inverse functors at the postcomposite `F ≫ i'`. -/
@[simp, stacks 04W9 "forward component of fixed-universe precomposition choice"]
theorem app (q q' : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    (F : X ⟶ X') :
    (choiceIso i' q q').hom.app F = (q.inverseIso q').hom.app (F ≫ i') := sorry

end choiceIso.hom

namespace choiceIso.inv

/-- The inverse component comparing two precomposition lifts is the inverse canonical comparison
of the chosen inverse functors at the postcomposite `F ≫ i'`. -/
@[simp, stacks 04W9 "inverse component of fixed-universe precomposition choice"]
theorem app (q q' : Functor.QuasiInverse (StackOver.Hom.precomp Y' i))
    (F : X ⟶ X') :
    (choiceIso i' q q').inv.app F = (q.inverseIso q').inv.app (F ≫ i') := sorry

end choiceIso.inv

end StackOver.Hom.PrecompLift.mapFunctor

end CategoryTheory
