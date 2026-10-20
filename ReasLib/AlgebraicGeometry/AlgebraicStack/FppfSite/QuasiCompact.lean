/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import ReasLib.CategoryTheory.Sites.QuasiCompact.TestSet
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import ReasLib.AlgebraicGeometry.GroupoidsOver.AffineSite
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated

/-!
# Quasi-compact test sets on the fppf site of an algebraic stack

The affine objects of a quasi-compact and quasi-separated algebraic stack form
a refining basis for its fppf topology and yield a quasi-compact test set.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.GrothendieckTopology.QuasiCompact
open CategoryTheory.GrothendieckTopology.QuasiCompact.TestSet

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- On a quasi-compact and quasi-separated algebraic stack, affine objects form
a basis with a finite terminal cover, finite refinements of covers, and finite
covers of products of sheafified representables. -/
instance affineObjects.instRefiningBasis {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X] :
    RefiningBasis X.fppfTopology (affineObjects X) :=
  sorry

/-- A quasi-compact and quasi-separated algebraic stack has a quasi-compact test
set on its associated fppf topology. -/
instance fppfTopology.instHasTestSet {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X] :
    HasTestSet X.fppfTopology :=
  sorry

end AlgebraicGeometry.AlgebraicStack
