/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos
public import ReasLib.CategoryTheory.Sites.QuasiCompact.TestSet

/-!
# Quasi-compact test sets on the small etale site

On a quasi-compact and absolutely quasi-separated algebraic space, affine objects
of the small etale site form a refining basis and yield a quasi-compact test set.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.GrothendieckTopology.QuasiCompact
open CategoryTheory.GrothendieckTopology.QuasiCompact.TestSet

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Affine objects of the small etale site form a refining basis under qcqs hypotheses. -/
instance affineEtaleObjects.instRefiningBasis {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    RefiningBasis (smallEtaleTopology X) (affineEtaleObjects X) :=
  sorry

/-- A qcqs algebraic space has a quasi-compact test set on its small etale topology. -/
instance smallEtaleTopology.instHasTestSet {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    HasTestSet (smallEtaleTopology X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
