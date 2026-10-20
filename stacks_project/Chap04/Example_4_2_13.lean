/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X X' : C} (f : X' ⟶ X)

/- Domain-style sampling for Example 4.2.13:
- primary domain: slice categories and their canonical forgetful/postcomposition functors.
- inspected owner declarations:
  `CategoryTheory.Over`,
  `CategoryTheory.Over.forget`,
  `CategoryTheory.Over.map`,
  `CategoryTheory.Over.mapForget_eq`.
- best owner abstraction: mathlib's slice-category owner `Over X`; the forgetful functor and
  postcomposition functoriality are derived owner API, not separate local structures or wrappers.
- primitive data: the base object `X : C` and, for the functoriality statements, a morphism
  `f : X' ⟶ X`.
- derived API: `Over.forget X`, `Over.map f`, and the coherence `Over.mapForget_eq f`.

Source/core/bridge triage:
- `source-facing`: the four textbook slice-category constructions recalled in this file.
- `core/canonical`: `Over`, `Over.forget`, `Over.map`, `Over.mapForget_eq`.
- `bridge/view`: none needed here, since the source notions already coincide with the mathlib
  owner declarations. -/

/- Example 4.2.13 (1): for an object `X` of a category `C`, the category of objects over `X` is
the slice category `Over X`, which in mathlib is the canonical owner for the textbook category
`C/X`; its objects are morphisms to `X`, and its morphisms are commutative triangles over `X`. -/
@[stacks 001G "slice category"]
#check (Over X : Type max u v)

/- Example 4.2.13 (2): the forgetful functor from the slice category `C/X` to `C` is
`Over.forget X`. -/
@[stacks 001G "slice projection"]
#check (Over.forget X : Over X ⥤ C)

/- Example 4.2.13 (3): a morphism `f : X' ⟶ X` induces the postcomposition functor
`Over.map f : Over X' ⥤ Over X`. -/
@[stacks 001G "postcomposition functor"]
#check (Over.map f : Over X' ⥤ Over X)

/- Example 4.2.13 (4): for a morphism `f : X' ⟶ X`, postcomposition along `f` followed by
forgetting to `C` agrees with the forgetful functor from `C/X'`; the owner-level coherence is
`Over.mapForget_eq f`. -/
@[stacks 001G "projection after postcomposition"]
#check (Over.mapForget_eq f : Over.map f ⋙ Over.forget X = Over.forget X')

end CategoryTheory
