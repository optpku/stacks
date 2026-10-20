/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine
public import stacks_project.Chap07.Definition_7_6_2_Site
public import stacks_project.Chap66.Definition_66_18_1_Site

/-!
# Affine étale site of an algebraic space

The affine étale site of an algebraic space `X` is the full subcategory of the small étale
site on objects whose source scheme is affine, with covering families those that cover in
`X_étale` and generate the same sieve on schemes as a finite standard étale cover.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.affineEtaleTopology :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.GrothendieckTopology
      (AlgebraicGeometry.AlgebraicSpace.affineEtaleSite X))
