/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.Topology.Sheaves.Sheaf
public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Preserves

/-!
# Categorical instances for open subsets

This file supplies finite-limit infrastructure for the category of open subsets and its slices.
The ambient category `Opens X` inherits finite limits from its complete lattice, while inverse
image preserves them through its canonical frame homomorphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice
open TopologicalSpace

universe u

namespace TopologicalSpace

/-- Inverse image of open subsets preserves finite limits. -/
instance Opens.map_preservesFiniteLimits {X Y : TopCat.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (Opens.map f) :=
  inferInstanceAs
    (PreservesFiniteLimits (OrderHomClass.toOrderHom f.frameHom).toFunctor)

/-- The slice over an open has a terminal object, represented by the identity of that open. -/
instance Opens.instHasTerminalOver
    (X : Type u) [TopologicalSpace X] (U : Opens X) :
    HasTerminal (Over U) :=
  CategoryTheory.Over.over_hasTerminal U

/-- The slice category over an open has binary products, computed by pullbacks of opens. -/
instance Opens.instHasBinaryProductsOver
    (X : Type u) [TopologicalSpace X] (U : Opens X) :
    HasBinaryProducts (Over U) :=
  CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback

/-- The slice category over an open has canonical finite products. -/
instance Opens.instHasFiniteProductsOver
    (X : Type u) [TopologicalSpace X] (U : Opens X) :
    HasFiniteProducts (Over U) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- Forgetting from the slice over an open preserves finite nonempty limits.  The nonempty
restriction is essential: the terminal object of `Over U` maps to `U`, not generally to `⊤`. -/
instance Opens.overForget_preservesFiniteNonemptyLimits (X : Type u)
    [TopologicalSpace X] (U : Opens X) :
    PreservesFiniteNonemptyLimits (Over.forget U) := sorry

end TopologicalSpace


