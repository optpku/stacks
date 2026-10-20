/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Basic
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Computations
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Functoriality
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Modification

/-!
# Pseudofunctorial postcomposition of costructured arrows

Aggregate import for postcomposition by a target `1`-morphism, its
computation rules, pairwise target-`1`-morphism coherence, and the local
target-`2`-cell action. The latter is contravariant, so `Functoriality` does
not claim a global target pseudofunctor. Import a leaf module when only the
owner, computation, comparison, or target-cell layer is needed.
-/
