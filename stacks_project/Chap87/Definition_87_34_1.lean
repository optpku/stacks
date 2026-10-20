/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleSite.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Definition 87.34.1 (1): let `S` be a scheme and let `X` be a formal algebraic
space over `S` with reduction `reduction X`. The small étale site `X_étale` of
`X` is the small étale site of `reduction X`, recorded as
`smallEtaleTopology X`. -/
@[stacks 0DEA] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.smallEtaleTopology :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
      (R : AlgebraicGeometry.FormalAlgebraicSpace.ReductionData X),
      GrothendieckTopology
        (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.smallEtaleSite R))

/- Definition 87.34.1 (2): the site `X_spaces,étale` of a formal algebraic space
`X` is the étale site of algebraic spaces over `reduction X`, recorded as
`spacesEtaleTopology X`. -/
@[stacks 0DEA] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.spacesEtaleTopology :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
      (R : AlgebraicGeometry.FormalAlgebraicSpace.ReductionData X),
      GrothendieckTopology
        (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.spacesEtaleSite R))

/- Definition 87.34.1 (3): the site `X_affine,étale` of a formal algebraic space
`X` is the affine étale site of `reduction X`, recorded as
`affineEtaleTopology X`. -/
@[stacks 0DEA] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.affineEtaleTopology :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
      (R : AlgebraicGeometry.FormalAlgebraicSpace.ReductionData X),
      GrothendieckTopology
        (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.affineEtaleSite R))
