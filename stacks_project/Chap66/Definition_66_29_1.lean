/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 66.29.1 (1): a quasi-coherent 𝒪_X-module on an algebraic space X over a scheme S
is a quasi-coherent module on the ringed site (X_étale, 𝒪_X) in the sense of
SheafOfModules.IsQuasicoherent. -/
@[stacks 03G9] #check (AlgebraicGeometry.AlgebraicSpace.quasiCoherentModuleProperty :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.ObjectProperty (AlgebraicGeometry.AlgebraicSpace.Modules X))

/- Definition 66.29.1 (2): the category of quasi-coherent sheaves on X is denoted QCoh(𝒪_X). -/
@[stacks 03G9] #check (AlgebraicGeometry.AlgebraicSpace.QCoh :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
