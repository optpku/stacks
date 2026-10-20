/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ChosenPresentation.Affine
import StacksCheckRecall

/-!
# Definition 34.4.8

The big and small étale sites of a scheme in a chosen big étale presentation,
together with their affine subsites and standard étale topologies.
-/

@[expose] public section

open CategoryTheory

universe u v

/- Definition 34.4.8 (1): the big étale site is the chosen slice equipped
with its induced slice topology. -/
@[stacks 021B] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.bigTopology :
    (X : AlgebraicGeometry.ChosenBigEtaleSite.{u, v}) →
      (S : X.carrier) →
        GrothendieckTopology (AlgebraicGeometry.ChosenBigEtaleSite.bigSite X S))

/- Definition 34.4.8 (2): the small étale site is the full subcategory on
objects whose represented structural morphism is étale, with inherited covers. -/
@[stacks 021B] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.smallTopology :
    (X : AlgebraicGeometry.ChosenBigEtaleSite.{u, v}) →
      (S : X.carrier) →
        GrothendieckTopology (AlgebraicGeometry.ChosenBigEtaleSite.smallSite X S))

/- Definition 34.4.8 (3): the big affine étale site is the affine full
subcategory of the chosen big slice with its standard étale topology. -/
@[stacks 021B] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.bigAffineTopology :
    (X : AlgebraicGeometry.ChosenBigEtaleSite.{u, v}) →
      (S : X.carrier) →
        GrothendieckTopology
          (AlgebraicGeometry.ChosenBigEtaleSite.bigAffineSite X S))

/- Definition 34.4.8 (4): the small affine étale site is the affine full
subcategory of the chosen small site with its standard étale topology. -/
@[stacks 021B] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.smallAffineTopology :
    (X : AlgebraicGeometry.ChosenBigEtaleSite.{u, v}) →
      (S : X.carrier) →
        GrothendieckTopology
          (AlgebraicGeometry.ChosenBigEtaleSite.smallAffineSite X S))

