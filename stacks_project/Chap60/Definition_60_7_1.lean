/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DividedPowers
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u v w

/- Definition 60.7.1: a divided power structure on an ideal sheaf `I` of a sheaf of
commutative rings `O` assigns a divided-power structure to every section ideal and is
compatible with restriction maps on sections. -/
@[stacks 07I2]
#check
  (DividedPowerIdealSheaf :
    ∀ {C : Type u} [Category.{v} C]
      (J : GrothendieckTopology C)
      [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
      (O : Sheaf J CommRingCat.{w})
      (I : Subobject (unitModule J O)), Type (max u w))
