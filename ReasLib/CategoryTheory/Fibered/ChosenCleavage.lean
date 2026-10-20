/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor.Comparison
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor.PullHom

/-!
# Choice-specialized infrastructure for fibred categories

This aggregate module exposes the application layer obtained by applying
`Functor.Cleavage.ofIsFibered`. Import the more precise `ChosenCleavage.Pseudofunctor` or
one of the focused `ChosenCleavage.Morphism` leaves (`Reindex`, `Composition`,
`Reindex.Calculus`, `Naturality`, `StrongTransformation`, `OwnerIso`, or `Modification`) when
only one layer is needed. `FiberedCategoryOver.strongTransHom` packages the full
action on owner `2`-morphisms. `Pseudofunctor.PullHom` gives the
descent-facing selected-cartesian calculation for Hom restrictions.
The selected pseudofunctor computation surface is grouped under
`Functor.FiberPseudofunctor.{map,mapIso,mapId,mapIdOp,mapComp,mapCompOp}`. Comparisons with an
explicit cleavage live under `Functor.Cleavage.toPseudofunctor.selectedEquivalence`, while
selected-cleavage core data is grouped under `Functor.Chosen`, with the direct owners `reindex`,
`cartesianHom`, `cartesianFactor`, and `verticalFactor`.
-/
