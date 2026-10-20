/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.StructureMap
public import stacks_project.Chap78.Definition_78_20_1_Quotient

/-!
# Compatibility with the legacy quotient atlas

The atlas retains its legacy quotient-stack type while using the canonical fppf atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The canonical fppf atlas with the definitionally compatible legacy quotient-stack type. -/
def atlas {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.U.left).p (quotientStack G).p :=
  fppfAtlas G

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.fppfAtlas :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      CartesianBasedFunctor (stackInSets G.U.left).p (fppfQuotientStack G).p)

end AlgebraicGeometry.GroupoidAlgebraicSpace
