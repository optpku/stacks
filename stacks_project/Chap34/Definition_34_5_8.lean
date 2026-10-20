/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.StandardAffine
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Definition 34.5.8

The canonical smooth topology on `Over S`, its affine restriction, and the
separate standard-affine smooth presentation are reusable scheme-site
infrastructure.  They are recalled directly from their neutral owners.
-/

#check AlgebraicGeometry.Scheme.smoothOverTopology
#check AlgebraicGeometry.Scheme.AffineOver
#check AlgebraicGeometry.Scheme.Smooth.StandardAffine.pretopology
#check AlgebraicGeometry.Scheme.Smooth.StandardAffine.presieve_mem

/- Definition 34.5.8: the big affine smooth site over `S` has affine
`S`-schemes as objects and finite standard smooth covering families. -/
@[stacks 03X0] #check
  (AlgebraicGeometry.Scheme.Smooth.StandardAffine.topology :
    (S : AlgebraicGeometry.Scheme.{u}) → CategoryTheory.GrothendieckTopology S.AffineOver)
