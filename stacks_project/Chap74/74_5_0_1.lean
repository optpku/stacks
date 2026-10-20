/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap74.«74_5_0_1_Comparison»
import StacksCheckRecall

@[expose] public section

universe u

variable {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)

/- 74.5.0.1: for a scheme S and an algebraic space X over S, the special-cocontinuous
inclusion of affine étale objects induces a morphism of ringed topoi
(Sh(X_affine,étale), 𝒪_X restricted to X_affine,étale) ⟶ (Sh(X_étale), 𝒪_X). -/
@[stacks 0H03] #check
  (RingedSite.Cocontinuous.toRingedTopos
    (AlgebraicGeometry.AlgebraicSpace.affineEtaleRingedInclusion X)
    (AlgebraicGeometry.AlgebraicSpace.affineEtaleComparison_structurePresheafMap X) :
    RingedSite.ToposHom (AlgebraicGeometry.AlgebraicSpace.affineRingedSite X)
      (AlgebraicGeometry.AlgebraicSpace.ringedSite X))
