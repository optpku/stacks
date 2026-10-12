/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fiberedness.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibred-category-over inertia projection fibredness

This leaf exposes the morphism-level specialization for `FiberedCategoryOver`.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

namespace FiberedCategoryOver

open scoped Bicategory

namespace RelativeInertia

namespace Projection

namespace Fibered

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- Lemma 4.34.1 (2) (Stacks 034H): relative inertia of a morphism of fibred categories has a
canonical fibred projection. -/
@[stacks 034H "relative-inertia projection is fibred"]
instance ofHom (F : X ⟶ Y) :
    (CategoryTheory.RelativeInertia.projection (toFunctor F) X.p).IsFibered := sorry
/- Proof strategy: apply `CategoryTheory.RelativeInertia.Projection.Fibered.ofCartesian` to
`toCartesianBasedFunctor F`. -/

end Fibered

end Projection

end RelativeInertia

end FiberedCategoryOver

end CategoryTheory
