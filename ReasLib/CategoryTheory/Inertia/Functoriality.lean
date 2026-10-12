/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Inertia.Functoriality.Computations
public import ReasLib.CategoryTheory.Inertia.Functoriality.StrongTrans

/-!
# Two-functoriality of inertia categories

Aggregate import for the inertia functoriality API. The implementation is split by
dependency layer:

* Comparison: identity and composition comparison isomorphisms;
* NatTrans: functor-category and natural-transformation action;
* Pseudofunctor: concrete strict-pseudofunctor owner;
* Strict: Cat-level strict-pseudofunctor projections;
* Computations: ordinary pseudofunctor projection formulas.

Import this module for the complete public API, or import a leaf module when only an earlier
dependency layer is needed.
-/
