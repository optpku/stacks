/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.KernelAnnihilation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap69.Definition_69_12_1_Instances

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.ClosedImmersion

/-!
# Coherent modules along closed immersions of algebraic spaces

The coherent closed-immersion equivalence is supplied by its shared mathematical owner.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S}
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
variable (i : Z ⟶ X) [IsClosedImmersion i]

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.ClosedImmersion.coherentPushforward_isEquivalence i :
    (AlgebraicGeometry.AlgebraicSpace.Modules.ClosedImmersion.coherentPushforward i).IsEquivalence)
