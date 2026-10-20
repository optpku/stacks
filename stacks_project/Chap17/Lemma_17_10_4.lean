/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open AlgebraicGeometry.RingedSpace.Hom

universe u

/- Lemma 17.10.4 (01BG): pullback of a quasi-coherent module sheaf along a morphism of ringed
spaces is quasi-coherent. -/
@[stacks 01BG]
#check fun {X Y : RingedSpace.{u}} (f : X ⟶ Y) (G : Y.Modules) [G.IsQuasicoherent] ↦
  (inferInstance : ((pullback f).obj G).IsQuasicoherent)
