/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Zariski.Affine
import StacksCheckRecall

/-!
# Definition 34.3.7: Zariski sites in a chosen presentation

The reusable owners define the big and small Zariski sites over a represented
base object, together with their affine full subsites and standard-cover
topologies.
-/

@[expose] public section

universe u v

/- Definition 34.3.7 (1): the big Zariski site over a represented base object
is the slice of the chosen big site with its induced topology. -/
@[stacks 020T] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.bigTopology :
    (X : AlgebraicGeometry.ChosenBigZariskiSite.{u, v}) →
      (S : X.carrier) →
        CategoryTheory.GrothendieckTopology
          (AlgebraicGeometry.ChosenBigZariskiSite.bigSite X S))

/- Definition 34.3.7 (2): the small Zariski site is the full subcategory on
represented open immersions, with coverings inherited from the big slice. -/
@[stacks 020T] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.smallTopology :
    (X : AlgebraicGeometry.ChosenBigZariskiSite.{u, v}) →
      (S : X.carrier) →
        CategoryTheory.GrothendieckTopology
          (AlgebraicGeometry.ChosenBigZariskiSite.smallSite X S))

/- Definition 34.3.7 (3): the big affine Zariski site is the affine full
subcategory of the chosen slice with its ambient-covering standard topology. -/
@[stacks 020T] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.bigAffineTopology :
    (X : AlgebraicGeometry.ChosenBigZariskiSite.{u, v}) →
      (S : X.carrier) →
        CategoryTheory.GrothendieckTopology
          (AlgebraicGeometry.ChosenBigZariskiSite.bigAffineSite X S))

/- Definition 34.3.7 (4): the small affine Zariski site is the affine full
subcategory of the chosen small site with its ambient-covering standard topology. -/
@[stacks 020T] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.smallAffineTopology :
    (X : AlgebraicGeometry.ChosenBigZariskiSite.{u, v}) →
      (S : X.carrier) →
        CategoryTheory.GrothendieckTopology
          (AlgebraicGeometry.ChosenBigZariskiSite.smallAffineSite X S))
