/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.CartesianClosed
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# Internal Hom in sheaf categories

The category of sheaves on a site is cartesian closed: for any sheaf `ℱ`,
the functor `· × ℱ` has a right adjoint `ihom ℱ`, the internal hom.
-/

@[expose] public section

universe w v u

/-! `Mathlib.CategoryTheory.Sites.CartesianClosed` is the canonical owner of the cartesian
closed structure on `Sheaf J (Type w)`, including the `ihom` API. -/
