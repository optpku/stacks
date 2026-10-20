/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.SimplicialScheme.Module.Quasicoherent
public import stacks_project.Chap85.Lemma_85_28_1_Ringed
public import stacks_project.Chap85.Lemma_85_28_1_Pullback

/-!
# Lemma 85.28.1

Pullback of quasi-coherent modules along a morphism of simplicial schemes remains
quasi-coherent on the Zariski ringed site of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/- Lemma 85.28.1: pullback along any morphism of simplicial schemes preserves
quasi-coherent modules on the simplicial Zariski sites. -/
@[stacks 07TI] #check
  (AlgebraicGeometry.SimplicialObject.modulePullback_isQuasicoherent :
    ∀ {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
      (F : SheafOfModules.{u} (structureSheaf U)) [F.IsQuasicoherent],
      ((modulePullback f).obj F).IsQuasicoherent)

end AlgebraicGeometry.SimplicialObject
