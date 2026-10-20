/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Basic
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Functoriality
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.FullyFaithful
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Canonical
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.PullFunctor
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Properties

/-!
# Descent data transported by an indexed functor

This compatibility import exposes the complete API for transport of descent data through an
identity-base indexed functor. Focused clients can instead import one of the following leaves:

* `DescentData.Basic` for the induced functor and component computations;
* `DescentData.Functoriality` for identity, composition, and modification actions;
* `DescentData.FullyFaithful` for full-faithful and equivalence transport;
* `DescentData.Canonical` for comparison with canonical descent data;
* `DescentData.PullFunctor` for comparison with a change of indexing family; or
* `DescentData.Properties` for prestack and stack transfer.

The identity-base hypothesis is essential: for an indexed functor over an arbitrary
`u : C ⥤ D`, a family of arrows in `C` does not describe descent data against all test objects
and arrows in `D`. Change-of-base applications should instead use the Hom-presheaf API in
`CategoryTheory.Sites.Descent.IndexedFunctor`.
-/
