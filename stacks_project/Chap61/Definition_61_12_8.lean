/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap61.Definition_61_12_8_Affine
public import stacks_project.Chap61.Definition_61_12_8_Presentation
import StacksCheckRecall

/-!
# Definition 61.12.8

The big, small, and big affine pro-étale sites of a scheme in a chosen big
pro-étale presentation.
-/

@[expose] public section

open CategoryTheory

universe u v

/- Definition 61.12.8 (1): the big pro-étale site is the chosen slice equipped
with its induced slice topology. -/
@[stacks 098K] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigTopology :
    (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) →
      (S : X.carrier) →
        GrothendieckTopology (AlgebraicGeometry.ChosenBigProetaleSite.bigSite X S))

/- Definition 61.12.8 (2): the small pro-étale site is the full subcategory on
objects whose represented structural morphism is weakly étale, with inherited
covers. -/
@[stacks 098K] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallTopology :
    (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) →
      (S : X.carrier) →
        GrothendieckTopology
          (AlgebraicGeometry.ChosenBigProetaleSite.smallSite X S))

/- Definition 61.12.8 (3): the big affine pro-étale site is the affine full
subcategory of the chosen big slice with its standard pro-étale topology. -/
@[stacks 098K] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineTopology :
    (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) →
      (S : X.carrier) →
        GrothendieckTopology
          (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineSite X S))

