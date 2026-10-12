/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Indexing
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Instances
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Value
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Denominator
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Domain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Everywhere

/-!
# Bounded and unbounded derived values at defined objects

This facade exports the indexing-diagram comparison, its induced pointwise value isomorphism,
denominator formulas, objectwise naturality, common-domain natural isomorphisms, and the global
comparison.  Import a leaf directly when only one layer is needed.
-/
