/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.Explicit
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.Chosen
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.PullFunctor
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.ChangeCleavage
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.Cover
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.FiberedCategoryOver.Action
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.FiberedCategoryOver.Equivalence
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.FiberedCategoryOver.PullFunctor

/-!
# Descent data transported by cartesian functors

This compatibility import exposes the complete descent-data transport API for
cartesian based functors and fibred-category morphisms.  Focused clients can
instead import one of the following leaves:

* `DescentData.Explicit` for transport with specified source and target cleavages, including
  fixed-cleavage equivalence criteria;
* `DescentData.Chosen` for the selected-cleavage specialization and its fixed-owner equivalences;
* `DescentData.PullFunctor` for cartesian-functor transport and a change of indexing family;
* `DescentData.ChangeCleavage` for comparison of two cleavages of one projection;
* `DescentData.Cover` for the action on descent data indexed by a bundled cover;
* `DescentData.FiberedCategoryOver.Action` for the direct action of fibred-category morphisms;
* `DescentData.FiberedCategoryOver.Equivalence` for full-faithfulness, equivalences, and
  prestack/stack transfer; or
* `DescentData.FiberedCategoryOver.PullFunctor` for pullback comparison of the direct action.

The compatibility path deliberately has no declarations of its own.  This keeps
the mathematical owners in small modules while preserving the established import
surface for existing clients.
-/
