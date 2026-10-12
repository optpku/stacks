/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.Tactic.CrossRefAttribute

/-!
# Refinements inducing isomorphisms on cokernels

A `CokernelRefinement f g` packages a commutative square from `f` to `g` whose induced
morphism on cokernels is an isomorphism.  Keeping this categorical notion independent of a
particular family of generators makes it reusable in presentation and dévissage arguments.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A commutative refinement square whose induced map on cokernels is an isomorphism. -/
@[stacks 093F "cokernel refinement"]
structure CokernelRefinement {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    [HasCokernel f] [HasCokernel g] where
  /-- The morphism between the sources of the horizontal maps. -/
  left : X ⟶ X'
  /-- The morphism between the targets of the horizontal maps. -/
  right : Y ⟶ Y'
  /-- The refinement square commutes. -/
  comm : f ≫ right = left ≫ g
  /-- The map on cokernels induced by the refinement square is an isomorphism. -/
  isIso_map : IsIso (cokernel.map f g left right comm)

end CategoryTheory.Limits
