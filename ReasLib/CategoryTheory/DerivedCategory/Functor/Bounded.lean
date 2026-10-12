/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.ComputesAt.Value
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.TwoSided.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.TwoSided.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.TwoSided.Naturality

/-!
# Additive functors and derived functors on bounded categories

This compatibility facade exports the bounded-below, bounded-above, and two-sided bounded induced
functors together with their inclusion, composition, naturality, and pointwise-definedness APIs.
It also exports the canonical bounded right- and left-derived functor facades, including their
value, comparison, degree, and naturality leaves.  Import a narrower leaf directly when only one
boundedness direction or comparison is required.
-/
