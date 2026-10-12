/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X X' : C} (f : X' ⟶ X)

/-
The source needs the coslice category `X/C`, its forgetful functor, precomposition by
`f : X' ⟶ X`, and the resulting strict functor equality. The verified candidates are the
lower-level `StructuredArrow`, the constructor API `Under.mk`/`Under.homMk`/`Under.w`, and the
owner-level declarations `Under`, `Under.forget`, `Under.map`, and `Under.mapForget_eq`. Directly
recalling the owner-level API is exact: `Under X` definitionally recovers the stated objects and
commutative triangles, while the remaining declarations have precisely the source directions and
equality. This introduces no generalization and leaves downstream users the full canonical
constructor and functor API without a project-local wrapper.
-/

/- Example 4.2.14 (1): for an object `X` of a category `C`, the category of objects under `X` is
the coslice category `Under X`, which in mathlib is the canonical owner for the textbook category
`X/C`. By definition this is `StructuredArrow X (𝟭 C)`, so its objects are morphisms with source
`X` and its morphisms are commutative triangles under `X`. -/
@[stacks 001H "under category"]
#check (Under X : Type max u v)

/- Example 4.2.14 (2): the forgetful functor from the coslice category `X/C` to `C` is
`Under.forget X`. -/
@[stacks 001H "forgetful functor"]
#check (Under.forget X : Under X ⥤ C)

/- Example 4.2.14 (3): a morphism `f : X' ⟶ X` induces the precomposition functor
`Under.map f : Under X ⥤ Under X'`. -/
@[stacks 001H "precomposition functor"]
#check (Under.map f : Under X ⥤ Under X')

/- Example 4.2.14 (4): precomposition along `f : X' ⟶ X` followed by forgetting to `C` agrees
with the forgetful functor from `X/C`, namely `Under.mapForget_eq f`. -/
@[stacks 001H "forgetful-functor coherence"]
#check (Under.mapForget_eq f : Under.map f ⋙ Under.forget X' = Under.forget X)

end CategoryTheory
