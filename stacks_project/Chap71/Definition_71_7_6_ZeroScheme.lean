/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap71.Definition_71_7_4_RegularSection

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection
import StacksCheckRecall

/-! # Zero schemes of sections

Stacks 0845 defines the zero subspace by the image of the actual dual-section map.
The public ZeroSection leaf owns that construction and its inclusion.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 71.7.6
The zero scheme of a section of an invertible sheaf is the closed subspace
defined by the image ideal of the dual-section map.
-/
@[stacks 0845] #check
  (AlgebraicGeometry.AlgebraicSpace.zeroScheme :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (ℒ : X.Modules) →
      [isInvertibleObject ℒ] → ℒ.sections → ClosedSubspace X)
#check AlgebraicGeometry.AlgebraicSpace.zeroIdealSubobject
#check AlgebraicGeometry.AlgebraicSpace.dualSectionHom
#check AlgebraicGeometry.AlgebraicSpace.zeroSchemeι
#check AlgebraicGeometry.AlgebraicSpace.zeroScheme_idealSheaf
