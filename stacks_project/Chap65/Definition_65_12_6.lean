/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Definition_65_12_6_Site
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 65.12.6: let `S` be a scheme and let `F` be an algebraic space over `S`.
A small Zariski site `F.smallZariskiTopology` of `F` is the Grothendieck topology on the
category of open subspaces of `F` (objects are open immersions into `F`, morphisms are
inclusions) whose coverings are the Zariski coverings of those open subspaces, obtained
by generating the topology from those covering families as for the opens site of a
topological space. -/
@[stacks 02YZ] #check (AlgebraicGeometry.AlgebraicSpace.smallZariskiTopology :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (F : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.GrothendieckTopology
      (AlgebraicGeometry.AlgebraicSpace.smallZariskiSite F))
