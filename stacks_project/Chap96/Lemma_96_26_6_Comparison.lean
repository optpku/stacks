/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.AffineFppf

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {S : Scheme.{u}} (X : GroupoidsOver S)

#check (AlgebraicGeometry.GroupoidsOver.affineSiteFppfTopology_eq X :
  AlgebraicGeometry.GroupoidsOver.affineSiteFppfTopology X =
    (AlgebraicGeometry.GroupoidsOver.affineSiteToAffineOver X).inheritedTopology
      (StandardTopology.Affine.topology StandardTopology.fppf S))
