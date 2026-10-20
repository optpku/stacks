/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Detection.Absolute
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of cartesian forgetting from absolute inertia

This leaf owns the universe-polymorphic cartesian based functor forgetting an
absolute-inertia automorphism. Its public computations are isolated in
`Cartesian.Forget.Computations`.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory.BasedCategory.Inertia

variable {C : Type u} [Category.{v} C]

/-- Forgetting an absolute-inertia automorphism, packaged as a heterogeneous cartesian functor.
Its functor data are exactly `BasedCategory.Inertia.forget X`; fibredness is used only to prove
preservation of strongly cartesian arrows. -/
@[stacks 042H "heterogeneous cartesian absolute-inertia structure map"]
def cartesianForget
    (X : BasedCategory.{vS, uS} C) [X.p.IsFibered] :
    CartesianBasedFunctor (BasedCategory.inertia X).p X.p :=
  CartesianBasedFunctor.ofBasedFunctor
    (BasedCategory.Inertia.forget X)
    (BasedCategory.Inertia.forget.preservesStronglyCartesian X)

end CategoryTheory.BasedCategory.Inertia

/- Axiom audit: `cartesianForget` stores the existing neutral forgetful based functor
definitionally. Any `sorryAx` dependency is confined to its Prop-valued cartesian-preservation
field. -/
