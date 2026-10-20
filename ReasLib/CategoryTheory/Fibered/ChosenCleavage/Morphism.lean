/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Reindex
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Reindex.Calculus
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Reindex.PullHom
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Composition
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Naturality
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.StrongTransformation
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.OwnerIso
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Modification
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.StrongTransformation.HomFunctor

/-!
# Choice-specialized fiber pseudofunctor morphisms

Aggregate import for the selected-cleavage morphism API.  Direct users
can import the focused `Reindex`, `Composition`, `Naturality`,
`StrongTransformation` (including its `HomFunctor` leaf),
`OwnerIso`, or `Modification` leaf matching the mathematical layer they use.
The preferred computation surface is grouped under the lowercase data owners
`FiberedCategoryOver.strongTrans`, `strongTrans₂`, `strongTransMap`, and `strongTransHom`,
together with the owner API below `FiberedCategoryOver.Reindex.mapIso`.

The universe-polymorphic, choice-free owner remains
`CartesianBasedFunctor.Reindex.mapIso`.
-/
