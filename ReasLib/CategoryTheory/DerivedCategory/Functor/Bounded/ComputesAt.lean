/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.ComputesAt.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.ComputesAt.Instances
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.ComputesAt.Value

@[expose] public section

/-!
# Bounded and unbounded computing objects

Compatibility facade for the bounded/unbounded computation equivalences, their directional
typeclass transport, and the associated bounded/unbounded value comparisons and naturality
laws.  Import a dedicated leaf when only one layer is needed.
-/
