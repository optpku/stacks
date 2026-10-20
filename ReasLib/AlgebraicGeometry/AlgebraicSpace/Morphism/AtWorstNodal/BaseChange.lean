/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal.EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AtWorstNodal

/-- The étale-local lift of at-worst-nodality of relative dimension one is stable
under arbitrary base change of morphisms of algebraic spaces. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    (etaleLocal (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) :
      MorphismProperty (AlgebraicSpace S)).IsStableUnderBaseChange := sorry

end AlgebraicGeometry.AlgebraicSpace.AtWorstNodal
